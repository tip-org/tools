{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.Concretise (intToNat, sortsToNat) where

import Tip.Core
import Tip.Parser
import Tip.Fresh
import Tip.Pretty
import Control.Monad.Writer
import Control.Applicative

import Data.Monoid

import qualified Data.Foldable as F

import qualified Data.Map as M
import Data.Map (Map)

import Data.Generics.Geniplate

import Tip.Utils

nat_theory :: Theory Id
Right nat_theory =
  parse
    "(declare-datatypes () ((Nat (Z) (S (p Nat))))) (define-fun-rec lt ((x Nat) (y Nat)) Bool (match y (case Z false) (case (S z) (match x (case Z true) (case (S n) (lt n z)))))) (define-fun-rec le ((x Nat) (y Nat)) Bool (match x (case Z true) (case (S z) (match y (case Z false) (case (S x2) (le z x2)))))) (define-fun-rec gt ((x Nat) (y Nat)) Bool (match x (case Z false) (case (S z) (match y (case Z true) (case (S x2) (gt z x2)))))) (define-fun-rec ge ((x Nat) (y Nat)) Bool (match y (case Z true) (case (S z) (match x (case Z false) (case (S x2) (ge x2 z)))))) (define-fun-rec equal ((x Nat) (y Nat)) Bool (match x (case Z (match y (case Z true) (case (S z) false))) (case (S x2) (match y (case Z false) (case (S y2) (equal x2 y2)))))) (define-fun unequal ((x Nat) (y Nat)) Bool (not (equal x y)))(check-sat)"

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

-- | Replaces the builtin Int to natural numbers,
--   if the only operations performed on are related to int ordering
intToNat :: forall a . Name a => Theory a -> Fresh (Theory a)
intToNat = replaceInt nat_theory

replaceInt :: forall a . Name a => Theory Id -> Theory a -> Fresh (Theory a)
replaceInt replacement_thy thy
  | any bad bs = return thy
  | otherwise =
     do nat_thy <- replacement_thy `renameWrt` thy

        let [nat] = thy_datatypes nat_thy

        let [lt,le,gt,ge,eq,ne] = thy_funcs nat_thy

        let replaceE :: Expr a -> Writer [Function a] (Expr a)
            replaceE e0@(Builtin b :@: (es@(e1:_))) =
              case b of
                NumLt -> ret lt
                NumLe -> ret le
                NumGt -> ret gt
                NumGe -> ret ge
                Equal    | exprType e1 == intType -> ret eq
                Distinct | exprType e1 == intType -> ret ne
                _ -> return e0
              where
              ret :: Function a -> Writer [Function a] (Expr a)
              ret op = tell [op] >> return (applyFunction op [] es)
            replaceE e0 = return e0

        let replaceT :: Type a -> Writer Any (Type a)
            replaceT (BuiltinType Integer) = tell (Any True) >> return (TyCon (data_name nat) [])
            replaceT t0 = return t0

        let (thy',     fns_used) = runWriter (transformBiM replaceE thy)
            (thy'',Any ty_used)  = runWriter (transformBiM replaceT thy')

        let used_nat_thy
              | null fns_used && not ty_used = emptyTheory
              | otherwise                    = nat_thy { thy_funcs = usort fns_used }

        return (thy'' `joinTheories` used_nat_thy)
  where
  bs :: [Builtin]
  bs = usort (universeBi thy)

  bad (Lit Int{}) = True
  bad NumAdd   = True
  bad NumSub   = True
  bad NumMul   = True
  bad NumDiv   = True
  bad IntDiv   = True
  bad IntMod   = True
  bad NumWiden = True
  bad _        = False

