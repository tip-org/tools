{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.Concretise (intToNat, sortsToNat) where

import Tip.Core
import Tip.Parser
import Tip.Fresh
import Tip.Pretty
import Control.Monad.Writer

import qualified Data.Foldable as F

import qualified Data.Map as M

import Data.Generics.Geniplate

import Tip.Utils

nat_theory :: Theory Id
Right nat_theory =
  parse $ unlines [
    "(declare-datatypes () ((Nat (Z) (S (p Nat)))))",
    "(define-fun-rec lt ((x Nat) (y Nat)) Bool",
    "  (match y",
    "    (case Z false)",
    "    (case (S z)",
    "      (match x",
    "        (case Z true)",
    "        (case (S n) (lt n z))))))",
    "(define-fun-rec le ((x Nat) (y Nat)) Bool",
    "  (match x",
    "    (case Z true)",
    "    (case (S z)",
    "      (match y",
    "        (case Z false)",
    "        (case (S x2) (le z x2))))))",
    "(define-fun-rec gt ((x Nat) (y Nat)) Bool",
    "  (lt y x))",
    "(define-fun-rec ge ((x Nat) (y Nat)) Bool",
    "  (le y x))",
    "(define-fun-rec plus ((x Nat) (y Nat)) Nat",
    "  (match x",
    "    (case Z y)",
    "    (case (S x) (S (plus x y)))))",
    -- 0 - S(x) is left undefined to better correspond to
    -- integer subtraction
    "(define-fun-rec minus ((x Nat) (y Nat)) Nat",
    "  (match x",
    "    (case Z Z)",
    "    (case (S x)",
    "      (match y",
    "        (case (S y) (minus x y))))))",
    "(define-fun-rec times ((x Nat) (y Nat)) Nat",
    "  (match x",
    "    (case Z Z)",
    "    (case (S x) (plus y (times x y)))))",
    "(define-fun-rec idiv ((x Nat) (y Nat)) Nat",
    "  (match (lt x y)",
    "    (case true Z)",
    "    (case default (S (idiv (minus x y) y)))))",
    "(define-fun-rec imod ((x Nat) (y Nat)) Nat",
    "  (match (lt x y)",
    "    (case true x)",
    "    (case default (imod (minus x y) y))))",
    "(check-sat)"]

renameWrt :: (Ord a,PrettyVar a,Name b) => Theory a -> f b -> Fresh (Theory b)
renameWrt thy _wrt =
  do rename_map <-
       M.fromList <$>
         sequence
           [ do n' <- freshNamed (varStr n)
                return (n,n')
           | n <- usort (F.toList thy)
           ]
     return (fmap (rename_map M.!) thy)

-- | Replaces abstract sorts with natural numbers
sortsToNat :: forall a . Name a => Theory a -> Fresh (Theory a)
sortsToNat = replaceSorts nat_theory

replaceSorts :: forall a . Name a => Theory Id -> Theory a -> Fresh (Theory a)
replaceSorts replacement_thy thy
  | null (thy_sorts thy) = return thy
  | otherwise =
      do nat_thy <- replacement_thy `renameWrt` thy
         let [nat] = thy_datatypes nat_thy
         let thy' =
               thy { thy_sorts = []
                   , thy_datatypes = nat:thy_datatypes thy
                   }
         let sorts = map sort_name (thy_sorts thy)
         let replace (TyCon s _) | s `elem` sorts = TyCon (data_name nat) []
             replace t0 = t0
         return (transformBi replace thy')

-- | Replaces the builtin Int with natural numbers,
intToNat :: forall a . Name a => Theory a -> Fresh (Theory a)
intToNat = replaceInt nat_theory

replaceInt :: forall a . Name a => Theory Id -> Theory a -> Fresh (Theory a)
replaceInt replacement_thy thy
  | any bad bs = return thy
  | otherwise =
     do nat_thy <- replacement_thy `renameWrt` thy

        let [nat] = thy_datatypes nat_thy
            [zeroCon, succCon] = data_cons nat
            zeroGlobal = constructor nat zeroCon []
            zero = Gbl zeroGlobal :@: []
            succGlobal = constructor nat succCon []
            succ e = Gbl succGlobal :@: [e]
            pred e = Gbl (projector nat succCon 0 []) :@: [e]

        let [lt,le,gt,ge,plus,minus,times,div,mod] = thy_funcs nat_thy

        let replaceE :: Expr a -> WriterT [Decl a] Fresh (Expr a)
            replaceE (Builtin NumAdd :@: [e, one]) | one == succ zero =
              return (succ e)
            replaceE (Builtin NumSub :@: [e, one]) | one == succ zero = do
              x <- lift $ freshLocal (TyCon (data_name nat) [])
              return $
                Match e [Case (ConPat succGlobal [x]) (pred e)]
            replaceE (Builtin NumLt :@: [_, z]) | z == zero = return (bool False)
            replaceE (Builtin NumLe :@: [z, _]) | z == zero = return (bool True)
            replaceE (Builtin NumGt :@: [z, _]) | z == zero = return (bool False)
            replaceE (Builtin NumGe :@: [_, z]) | z == zero = return (bool True)
            replaceE e0@(Builtin b :@: (es@(e1:_)))
              | exprType e1 `elem` [BuiltinType Integer, TyCon (data_name nat) []] =
              case b of
                NumLt -> ret lt
                NumLe -> ret le
                NumGt -> tell [FuncDecl lt] >> ret gt
                NumGe -> tell [FuncDecl le] >> ret ge
                NumAdd -> ret plus
                NumSub -> ret minus
                NumMul -> tell [FuncDecl plus] >> ret times
                IntDiv -> tell [FuncDecl lt, FuncDecl minus] >> ret div
                IntMod -> tell [FuncDecl lt, FuncDecl minus] >> ret mod
                _ -> return e0
              where
              ret :: Function a -> WriterT [Decl a] Fresh (Expr a)
              ret op = tell [FuncDecl op] >> return (applyFunction op [] es)
            replaceE (Builtin (Lit (Int n)) :@: []) =
              return (foldr (const succ) zero [1..n])
            replaceE e0 = return e0

        let replaceT :: Type a -> Writer Any (Type a)
            replaceT (BuiltinType Integer) = tell (Any True) >> return (TyCon (data_name nat) [])
            replaceT t0 = return t0

        (thy', fns_used) <- runWriterT (transformBiM replaceE thy)
        let (thy'', Any ty_used)  = runWriter (transformBiM replaceT thy')

        let used_nat_thy
              | null fns_used && not ty_used = emptyTheory
              | otherwise = declsToTheory (DataDecl nat:usort fns_used)

        return (thy'' `joinTheories` used_nat_thy)
  where
  bs :: [Builtin]
  bs = usort (universeBi thy)

  bad (Lit (Int n)) | n > 100 = True
  bad NumDiv   = True
  bad NumWiden = True
  bad _        = False

