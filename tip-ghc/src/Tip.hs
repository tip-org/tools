{-# LANGUAGE TypeOperators, FlexibleInstances #-}
-- | A property language for TIP properties.
-- XXXXX fill this in.
module Tip
    ( Equality
    , (:=>:)
    , And
    , Or
    , Neg
    , Forall
    , Exists
    , (===)
    , (=/=)
    , bool
    , (==>)
    , (.&&.)
    , (.||.)
    , neg
    , question
    , forAll
    , exists
    , module Test.QuickCheck
    , module Tip.GHC.Annotations
    ) where

import Test.QuickCheck hiding ((===), (==>), (.&&.), (.||.), forAll)
import qualified Test.QuickCheck as QC
import Tip.GHC.Annotations()

infix 3 ===
infix 3 =/=
infixr 2 .&&.
infixr 1 .||.
infixr 0 ==>
infixr 0 :=>:

-- | The property data type

data Equality a = a :=: a
data a :=>: b = Given a b
data And a b = And a b
data Or a b = Or a b
data Neg a = Neg a
data Forall a b = Forall (a -> b)
data Exists a b = Exists (a -> b)

-- | Equality
(===) :: a -> a -> Equality a
(===) = (:=:)

-- | Inequality
(=/=) :: a -> a -> Neg (Equality a)
u =/= v = Neg (u === v)

-- | A synonym for '===', but for booleans
bool :: Bool -> Equality Bool
bool lhs = lhs === True

-- | Implication
(==>) :: a -> b -> a :=>: b
(==>) = Given

-- | Conjunction
(.&&.) :: a -> b -> And a b
(.&&.) = And

-- | Disjunction
(.||.) :: a -> b -> Or a b
(.||.) = Or

-- | Negation
neg :: a -> Neg a
neg = Neg

-- | Question (same as negation)
question :: a -> Neg a
question = Neg

-- | Universal quantification
forAll :: (a -> b) -> Forall a b
forAll = Forall

-- | Existential quantification
exists :: (a -> b) -> Exists a b
exists = Exists

instance (Eq a, Show a) => Testable (Equality a) where
  property (x :=: y) = x QC.=== y

instance Testable b => Testable (Bool :=>: b) where
  property (Given x p) = x QC.==> p

instance Testable b => Testable (Neg Bool :=>: b) where
  property (Given (Neg x) p) = not x QC.==> p

instance Testable (Neg Bool) where
  property (Neg x) = property (not x)

instance (Eq a, Show a, Testable b) => Testable (Equality a :=>: b) where
  property (Given (x :=: y) p) = x == y QC.==> p

instance (Testable a, Testable b) => Testable (And a b) where
  property (And p q) = p QC..&&. q

instance (Testable a, Testable b) => Testable (Or a b) where
  property (Or p q)  = p QC..||. q

instance (Arbitrary a, Show a, Testable b) => Testable (Forall a b) where
  property (Forall p) = property p

