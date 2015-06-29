{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Tip.Utils.Specialiser
    (specialise, Rule(..), Expr(..),
     Void, absurd,
     Closed, subtermRules, subterms, Subst, Inst) where

import Tip.Fresh
import Tip.Utils
import Tip.Pretty

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Generics.Genifunctors

import Text.PrettyPrint

data Expr c a = Var a | Con c [Expr c a]
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Rule c a = Rule
  { rule_pre  :: [Expr c a]
  -- ^ The trigger(s).
  , rule_post :: Expr c a
  -- ^ The action. The variables here must be a subset of those in pre.
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

return []

bimapRule :: (c -> c') -> (a -> a') -> Rule c a -> Rule c' a'
bimapRule = $(genFmap ''Rule)

mapRuleOrd :: (c -> c') -> Rule c a -> Rule c' a
mapRuleOrd c = bimapRule c id

instance (Pretty c,Pretty a) => Pretty (Expr c a) where
  pp (Var x)    = pp x
  pp (Con k es) = pp k <+> parens (fsep (punctuate "," (map pp es)))

instance (Pretty c,Pretty a) => Pretty (Rule c a) where
  pp (Rule ps q) = parens (fsep (punctuate "," (map pp ps))) <+> "=>" $\ pp q

subtermRules :: Rule c a -> [Rule c a]
subtermRules (Rule p q) = map (Rule p) (subterms q)

subterms :: Expr c a -> [Expr c a]
subterms e = e : case e of Var a    -> []
                           Con _ es -> concatMap subterms es

ruleVars :: Ord a => Rule c a -> [a]
ruleVars (Rule ps q) = usort $ concatMap go (q:ps)
  where
  go (Var x) = [x]
  go (Con c es) = concatMap go es

type Closed c = Expr c Void

data Sk c = Old c | Sk Int
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Pretty c => Pretty (Sk c) where
  pp (Old c) = pp c
  pp (Sk i)  = int i

instance Ord c => Name (Sk c) where
  fresh = Sk <$> fresh

instance PrettyVar (Sk c) where
  varStr _ = show ""

unSkolem :: Closed (Sk c) -> Expr c Int
unSkolem (Con (Old k) es) = Con k (map unSkolem es)
unSkolem (Con (Sk i) [])  = Var i

varOf :: Eq a => a -> Expr c a -> Bool
x `varOf` Var y    = x == y
x `varOf` Con _ es = any (x `varOf`) es

specialise :: forall d c a . (Ord d,Ord c,Ord a) =>
    [(d,[Rule c a])] -> ([(d,Subst a Void c)],[d])
specialise decl_rules = (which (usort (go [close [] s | (_,Rule [] s) <- named_rules])), scary)
  where
  free0,free,scary :: [d]
  (usort -> free0,usort -> scary) = separate [ (d,r) | (d,rs) <- decl_rules, r <- rs ]
  free = free0 \\ scary

  named_rules :: [(d,Rule c a)]
  named_rules = [ (d,r) | (d,rules) <- decl_rules, d `elem` free, r <- rules ]

  go :: [Closed c] -> [Closed c]
  go insts
    | null (new_insts \\ insts) = []
    | otherwise                 = new_insts `union` go (new_insts `union` insts)
    where
    new_insts = usort $ map (snd . snd) new
    new = step named_rules insts

  which :: [Closed c] -> [(d,Subst a Void c)]
  which cls = usort [ (d,i) | (d,(i,_)) <- step named_rules cls ]

-- Return the safe rules, and the scary rules
separate :: (Ord a,Ord c) => [(name,Rule c a)] -> ([name],[name])
separate = go []
  where
  go rs ((n,r):xs)
    | terminating (r:rs) = let (a,b) = go (r:rs) xs in (n:a,b  )
    | otherwise          = let (a,b) = go rs     xs in (  a,n:b)
  go _ _ = ([],[])

terminating :: forall a c . (Ord a,Ord c) => [Rule c a] -> Bool
terminating (map (mapRuleOrd Old) -> rs) = go 10 S.empty (usort (inst rs))
  where
  go :: Int -> Set (Closed (Sk c)) -> [Closed (Sk c)] -> Bool
  {-
  go i visited new
    | traceShow ("go" $\ sep ["i:" $\ pp i
                             ,"visited:" $\ pp (S.toList visited)
                             ,"new:" $\ pp new
                             ])
                False = undefined
  -}
  go 0 _ _  = False
  go _ _ [] = True
  go i visited new =
    let both = visited `S.union` S.fromList new
    in  go (i-1) both (unnamedStep rs new \\ S.toList both)

union :: Ord a => [a] -> [a] -> [a]
union (S.fromList -> s1) (S.fromList -> s2) = S.toList (s1 `S.union` s2)

(\\) :: Ord a => [a] -> [a] -> [a]
(\\) (S.fromList -> s1) (S.fromList -> s2) = S.toList (s1 S.\\ s2)

inst :: (Ord a,Ord c) => [Rule (Sk c) a] -> [Closed (Sk c)]
inst rules = runFresh $
  do i <- fresh
     return (concatMap (instPre i) rules)

instPre :: (Ord a,Ord c) => Sk c -> Rule (Sk c) a -> [Closed (Sk c)]
instPre c r =
  let su = [ (v,Con c []) | v <- ruleVars r ]
  in  map (close su) (rule_pre r)

close :: Eq a => [(a,Closed c)] -> Expr c a -> Closed c
close su (Var v)    = fromMaybe (error "close") (lookup v su)
close su (Con c es) = Con c (map (close su) es)

unnamedStep :: (Ord c,Ord a) => [Rule c a] -> [Closed c] -> [Closed c]
unnamedStep rs = usort . map (snd . snd) . step (map ((,) ()) rs)

step :: (Ord name,Ord c,Ord a) => [(name,Rule c a)] -> [Closed c] -> [(name,Inst a c)]
step rs es = usort [ (name,i) | (name,r) <- rs, i <- activateOne r es ]

type Inst a c = (Subst a Void c,Closed c)

activateOne :: (Ord c,Ord a) => Rule c a -> [Closed c] -> [Inst a c]
activateOne (Rule ps q) es = [ (su,close su q) | su <- go ps ]
  where
    go []     = [[]] -- success, return the empty substitution
    go (p:ps) = [ su
                | e <- es
                , Just sua <- [match p e]
                , sub <- go ps
                , Just su <- [merge sua sub]
                ]


type Subst a b c = [(a,Expr c b)]

merge :: (Ord a,Ord b,Ord c) => Subst a b c -> Subst a b c -> Maybe (Subst a b c)
merge xs ys =
  do guard (and [ maybe True (e ==) (lookup v ys) | (v,e) <- xs ])
     Just (unionOn fst xs ys)

merges :: (Ord a,Ord b,Ord c) => [Subst a b c] -> Maybe (Subst a b c)
merges = foldM merge []

match :: (Ord a,Ord b,Ord c) => Expr c a -> Expr c b -> Maybe (Subst a b c)
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

