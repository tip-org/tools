{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
module Tip.Utils.Specialiser
    (specialise, specialiseWithWeakener, specialiseWithWeakener', Rule(..), Expr(..),
     Verbosity(..),
     Void, absurd,
     Closed, subtermRules, subterms, Subst, Inst) where

#include "errors.h"
import Tip.Fresh
import Tip.Utils
import Tip.Pretty

import Control.Arrow (first)
import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Data.Generics.Genifunctors

import Text.PrettyPrint

import Debug.Trace

data Verbosity = Silent | Verbose
  deriving (Eq,Ord,Show,Read,Enum,Bounded)

data Expr c a = Var a | Con c [Expr c a]
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Rule c a = [Expr c a] :==> Expr c a
  -- The variables on the rhs must be a subset of those in lhs.
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

return []

type Ctx a = (Ord a,Pretty a)

bimapRule :: (c -> c') -> (a -> a') -> Rule c a -> Rule c' a'
bimapRule = $(genFmap ''Rule)

mapRuleCtx :: (c -> c') -> Rule c a -> Rule c' a
mapRuleCtx c = bimapRule c id

instance (Pretty c,Pretty a) => Pretty (Expr c a) where
  pp (Var x)    = pp x
  pp (Con k es) = pp k <+> parens (fsep (punctuate "," (map pp es)))

instance (Pretty c,Pretty a) => Pretty (Rule c a) where
  pp (ps :==> q) = parens (fsep (punctuate "," (map pp ps))) <+> "=>" $\ pp q

subtermRules :: Rule c a -> [Rule c a]
subtermRules (p :==> q) = map (p :==>) (subterms q)

subterms :: Expr c a -> [Expr c a]
subterms e = e : case e of Var a    -> []
                           Con _ es -> concatMap subterms es

ruleVars :: Ctx a => Rule c a -> [a]
ruleVars (ps :==> q) = usort $ concatMap go (q:ps)
  where
  go (Var x) = [x]
  go (Con c es) = concatMap go es

type Closed c = Expr c Void

varOf :: Eq a => a -> Expr c a -> Bool
x `varOf` Var y    = x == y
x `varOf` Con _ es = any (x `varOf`) es

specialiseWithWeakener' ::
    forall d c a . (Ctx d,Ctx c,Ctx a) =>
    (d -> Rule c a -> Maybe (Rule c a)) -> [(d,Rule c a)] ->
    ([(d,Subst a Void c)],[(d,(Rule c a,Rule c a))],[(d,Rule c a)])
specialiseWithWeakener' weaken rules
  = let ds   = map fst rules
        to   :: Map Int d
        to   = M.fromList (zip [0..] ds)
        from :: Map d Int
        from = M.fromList (zip ds [0..])
        (ok,weaks,rest) = specialiseWithWeakener
                        (\ i -> weaken (to M.! i))
                        [(from M.! d,r) | (d,r) <- rules]
    in  ( map (first (to M.!)) ok
        , map (first (to M.!)) weaks
        , map (first (to M.!)) rest
        )


specialiseWithWeakener ::
    forall d c a . (Ctx d,Ctx c,Ctx a) =>
    (d -> Rule c a -> Maybe (Rule c a)) -> [(d,Rule c a)] ->
    ([(d,Subst a Void c)],[(d,(Rule c a,Rule c a))],[(d,Rule c a)])
specialiseWithWeakener weaken = go
  where
  go rules =
    case firstNonterm rules of
      Nothing -> (specialise rules,[],[])
      Just (ok,(d,prob),rest) ->
        case weaken d prob of
          r | traceShow ("wk" $\ pp d $\ pp prob $\ maybe "" pp r) False -> undefined
          Just weakened -> let (insts,weaks,probs) = go (ok ++ [(d,weakened)] ++ rest)
                           in  (insts,(d,(prob,weakened)):weaks,probs)
          Nothing       -> let (insts,weaks,probs) = go (ok ++ rest)
                           in  (insts,weaks,(d,prob):probs)

firstNonterm ::
    forall d c a . (Ctx d,Ctx c,Ctx a) =>
    [(d,Rule c a)] -> Maybe ([(d,Rule c a)],(d,Rule c a),[(d,Rule c a)])
firstNonterm rules =
  case binsearch (\ i -> traceShow ("binsearch" $\ pp i) $ not $ terminating (map snd $ take i rules)) 0 (length rules) of
    Nothing -> Nothing
    Just i  -> let (ok,prob:rest) = splitAt (i-1) rules
               in  Just (ok,prob,rest)

-- loops if it does not terminate
specialise :: forall d c a . (Ctx d,Ctx c,Ctx a) => [(d,Rule c a)] -> [(d,Subst a Void c)]
specialise rules = let res = FROMJUST("Cannot fail")(steps (-1) rules)
                   in  [ (d,su) | (d,(su,_)) <- res ]

close :: Eq a => [(a,Closed c)] -> Expr c a -> Closed c
close su (Var v)    = fromMaybe (ERROR("Unbound variable, did you run --type-skolem-conjecture?")) (lookup v su)
close su (Con c es) = Con c (map (close su) es)

terminating :: forall a c . (Ctx a,Ctx c) => [Rule c a] -> Bool
terminating rs = isJust (steps 5 (map ((,) ()) rs))

steps :: forall name c a . (Ctx name,Ctx c,Ctx a) =>
         Int -> [(name,Rule c a)] -> Maybe [(name,Inst a c)]
steps max_steps rules = fmap usort (go max_steps [])
  where
  go :: Int -> [Closed c] -> Maybe [(name,Inst a c)]
  go i insts | traceShow ("steps" $\ pp i $\ pp insts) False = undefined
  go 0 _ = Nothing
  go i insts
    | null (new_insts \\ insts) = Just []
    | otherwise                 = fmap (new++) (go (i-1) (new_insts `union` insts))
    where
    new_insts = usort $ map (snd . snd) new
    new       = step rules insts

step :: (Ctx name,Ctx c,Ctx a) => [(name,Rule c a)] -> [Closed c] -> [(name,Inst a c)]
step rs es = usort [ (name,i) | (name,r) <- rs, i <- activateOne r es ]

type Inst a c = (Subst a Void c,Closed c)

activateOne :: (Ctx c,Ctx a) => Rule c a -> [Closed c] -> [Inst a c]
activateOne (ps :==> q) es = [ (su,close su q) | su <- go ps ]
  where
    go []     = [[]] -- success, return the empty substitution
    go (p:ps) = [ su
                | e <- es
                , Just sua <- [match p e]
                , sub <- go ps
                , Just su <- [merge sua sub]
                ]


type Subst a b c = [(a,Expr c b)]

merge :: (Ctx a,Ctx b,Ctx c) => Subst a b c -> Subst a b c -> Maybe (Subst a b c)
merge xs ys =
  do guard (and [ maybe True (e ==) (lookup v ys) | (v,e) <- xs ])
     Just (unionOn fst xs ys)

merges :: (Ctx a,Ctx b,Ctx c) => [Subst a b c] -> Maybe (Subst a b c)
merges = foldM merge []

match :: (Ctx a,Ctx b,Ctx c) => Expr c a -> Expr c b -> Maybe (Subst a b c)
match (Var x) e = Just [(x,e)]
match (Con c xs) (Con d ys)
  | c == d
  , length xs == length ys
  = merges =<< zipWithM match xs ys
match _ _ = Nothing

data Void = Void !Void
  deriving (Eq,Ord,Show)

absurd :: Void -> a
absurd (Void v) = absurd v

instance Pretty Void where
  pp = absurd

sbin :: Ctx a => (Set a -> Set a -> Set a) -> [a] -> [a] -> [a]
sbin op = \ xs ys -> S.toList (S.fromList xs `op` S.fromList ys)

union,(\\) :: Ctx a => [a] -> [a] -> [a]
union = sbin S.union
(\\)  = sbin (S.\\)

