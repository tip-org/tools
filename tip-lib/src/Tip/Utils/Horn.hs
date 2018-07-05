{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE TypeFamilies, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, CPP, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Compute all consequences of a set of Horn clauses
module Tip.Utils.Horn (rule, specialiseRules, numberVars, Expr(..), Rule(..)) where
import Twee.Base hiding (Var, Fun, App, Pretty)
import qualified Twee.Base as Twee
import qualified Twee.Index as Index
import Control.Monad
import Data.Maybe
import Data.Generics.Geniplate
import Tip.Pretty
import qualified Data.Set as Set
import Data.Typeable
import Twee.Label
import qualified Text.PrettyPrint.HughesPJ as Pretty

data Expr v c = Var v | App c [Expr v c]
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance (Pretty v, Pretty c) => Pretty (Expr v c) where
  pp (Var x) = text "V" Pretty.<> pp x
  pp (App c []) = pp c
  pp (App c as) = parens (pp c $\ fsep (map pp as))

numberVars :: (Typeable v, Ord v) => Expr v c -> Expr Int c
numberVars (Var x) = Var (fromIntegral (labelNum (label x)))
numberVars (App f xs) = App f (map numberVars xs)

exprToTwee :: (Typeable a, Ord a) => Expr Int a -> Term a
exprToTwee = build . toTwee
  where
    toTwee (Var x) = var (V x)
    toTwee (App f xs) = app (fun f) (map toTwee xs)

exprFromTwee :: Term a -> Expr Int a
exprFromTwee (Twee.Var (V x)) = Var x
exprFromTwee (Twee.App f xs) = App (fun_value f) (map exprFromTwee (unpack xs))

data Rule a =
    Fact a
  | a :=>: Rule a
  deriving (Eq, Ord, Functor)

instance Symbolic a => Symbolic (Rule a) where
  type ConstantOf (Rule a) = ConstantOf a
  termsDL (Fact t) = termsDL t
  termsDL (t :=>: c) = termsDL t `mplus` termsDL c
  subst_ sub (Fact t) = Fact (subst_ sub t)
  subst_ sub (t :=>: c) = subst_ sub t :=>: subst_ sub c

instance Pretty a => Pretty (Rule a) where
  pp (Fact e)   = pp e
  pp (e :=>: r) = pp e <+> "=>" $\ pp r

rule :: [a] -> a -> Rule a
rule ts t = foldr (:=>:) (Fact t) ts

consequences :: (Ord a, Typeable a, Pretty a) => [Rule (Term a)] -> [Term a]
consequences cs = loop Set.empty Index.empty Set.empty cs
  where
    loop facts _ _ [] = Set.toList facts
    loop facts rules seen (c0:cs)
      | c `Set.member` seen =
        loop facts rules seen cs
      | otherwise =
        let seen'= Set.insert c seen in
        case c of
          Fact t ->
            loop (Set.insert t facts) rules seen'
              (derive [t] (Index.approxMatches t rules) ++ cs)
          t :=>: _ ->
            loop facts (Index.insert t c rules) seen'
              (derive (Set.toList facts) [c] ++ cs)
      where
        c = canonicalise c0

    derive ts rules =
      [ subst sub rule
      | t <- ts,
        u :=>: rule <- rules,
        sub <- maybeToList (match u t) ]
    
specialiseRules :: (Typeable a, Ord a, Pretty a) => [Rule (Expr Int a)] -> [Expr Int a]
specialiseRules =
  map exprFromTwee . consequences . map (fmap exprToTwee)

return []

instanceTransformBi [t| forall a . (a,[Rule a]) |]
instanceTransformBi [t| forall a . (a,Rule a) |]
instanceTransformBi [t| forall c a . (Expr c a,Expr c a) |]

