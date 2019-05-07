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
    "(declare-datatype Nat ((zero) (succ (p Nat))))",
    "(define-fun-rec lt :definition :source |<|",
      "((x Nat) (y Nat)) Bool",
      "(match y",
        "((zero false)",
         "((succ z)",
           "(match x",
             "((zero true)",
              "((succ n) (lt n z))))))))",
    "(define-fun-rec leq :definition :source |<=|",
      "((x Nat) (y Nat)) Bool",
      "(match x",
        "((zero true)",
         "((succ z)",
           "(match y",
             "((zero false)",
              "((succ x2) (leq z x2))))))))",
    "(define-fun-rec gt :definition :source |>|",
      "((x Nat) (y Nat)) Bool",
      "(lt y x))",
    "(define-fun-rec geq :definition :source |>=|",
      "((x Nat) (y Nat)) Bool",
      "(leq y x))",
    "(define-fun-rec plus :definition :source |+|",
      "((x Nat) (y Nat)) Nat",
      "(match x",
        "((zero y)",
         "((succ x) (succ (plus x y))))))",
    "(define-fun-rec minus :definition :source |-|",
      "((x Nat) (y Nat)) Nat",
      "(match x",
        "((zero zero)",
         "((succ x)",
           "(match y",
             "(((succ y) (minus x y))",
               "(zero zero)))))))",
    "(define-fun-rec times :definition :source |*|",
      "((x Nat) (y Nat)) Nat",
      "(match x",
        "((zero zero)",
         "((succ x) (plus y (times x y))))))",
    "(define-fun-rec idiv :definition :source |div|",
      "((x Nat) (y Nat)) Nat",
      "(match (lt x y)",
        "((true zero)",
         "(_ (succ (idiv (minus x y) y))))))",
    "(define-fun-rec imod :definition :source |mod|",
      "((x Nat) (y Nat)) Nat",
      "(match (lt x y)",
        "((true x)",
         "(_ (imod (minus x y) y)))))",
    "(define-fun-rec even :definition :source |even|",
      "((x Nat)) Bool",
      "(match x",
        "((zero true)",
         "((succ y) (not (even y))))))",
    "(assert :axiom |commutativity of +|",
      "(forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))",
    "(assert :axiom |associativity of +|",
      "(forall ((x Nat) (y Nat) (z Nat)) (= (plus x (plus y z)) (plus (plus x y) z))))",
    "(assert :axiom |identity for +|",
      "(forall ((x Nat)) (= (plus x zero) x)))",
    "(assert :axiom |identity for +|",
      "(forall ((x Nat)) (= (plus zero x) x)))",
    "(assert :axiom |commutativity of *|",
      "(forall ((x Nat) (y Nat)) (= (times x y) (times y x))))",
    "(assert :axiom |associativity of *|",
      "(forall ((x Nat) (y Nat) (z Nat)) (= (times x (times y z)) (times (times x y) z))))",
    "(assert :axiom |identity for *|",
      "(forall ((x Nat)) (= (times x (succ zero)) x)))",
    "(assert :axiom |identity for *|",
      "(forall ((x Nat)) (= (times (succ zero) x) x)))",
    "(assert :axiom |zero for *|",
      "(forall ((x Nat)) (= (times x zero) zero)))",
    "(assert :axiom |zero for *|",
      "(forall ((x Nat)) (= (times zero x) zero)))",
    "(assert :axiom |distributivity|",
      "(forall ((x Nat) (y Nat) (z Nat)) (= (times x (plus y z)) (plus (times x y) (times x z)))))",
    "(assert :axiom |distributivity|",
      "(forall ((x Nat) (y Nat) (z Nat)) (= (times (plus x y) z) (plus (times x z) (times y z)))))"]

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

        let [lt,le,gt,ge,plus,minus,times,div,mod,even] = thy_funcs nat_thy
            [plus1, plus2, plus3, plus4,
             times1, times2, times3, times4, times5, times6, times7, times8] =
              thy_asserts nat_thy
            plus_ax =
              [plus1, plus2, plus3, plus4]
            times_ax =
              [times1, times2, times3, times4, times5, times6, times7, times8]

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
            replaceE (Builtin IntMod :@: [e, two]) | two == succ (succ zero) = do
              tell [FuncDecl even]
              return (makeIf (applyFunction even [] [e]) zero (succ zero))
            replaceE e0@(Builtin b :@: (es@(e1:_)))
              | exprType e1 `elem` [BuiltinType Integer, TyCon (data_name nat) []] =
                case builtinOp b of
                  Nothing ->
                    return e0
                  Just f -> do
                    builtin b
                    return (applyFunction f [] es)

            replaceE (Builtin (Lit (Int n)) :@: []) =
              return (foldr (const succ) zero [1..n])
            replaceE e0 = return e0

            builtin :: Builtin -> WriterT [Decl a] Fresh ()
            builtin b = do
              builtinSpecial b
              case builtinOp b of
                Nothing -> return ()
                Just f -> tell [FuncDecl f]

            builtinSpecial :: Builtin -> WriterT [Decl a] Fresh ()
            builtinSpecial NumGt =
              builtin NumLt
            builtinSpecial NumGe =
              builtin NumLe
            builtinSpecial NumAdd =
              tell (map AssertDecl plus_ax)
            builtinSpecial NumMul = do
              builtin NumAdd
              tell (map AssertDecl times_ax)
            builtinSpecial IntDiv = do
              builtin NumLt
              builtin NumSub
            builtinSpecial IntMod = do
              builtin NumLt
              builtin NumSub
            builtinSpecial _ = return ()

            builtinOp :: Builtin -> Maybe (Function a)
            builtinOp NumLt = Just lt
            builtinOp NumLe = Just le
            builtinOp NumGt = Just gt
            builtinOp NumGe = Just ge
            builtinOp NumAdd = Just plus
            builtinOp NumSub = Just minus
            builtinOp NumMul = Just times
            builtinOp IntDiv = Just div
            builtinOp IntMod = Just mod
            builtinOp _ = Nothing

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

