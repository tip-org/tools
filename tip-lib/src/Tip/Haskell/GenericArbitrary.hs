{-# LANGUAGE DeriveFunctor, FlexibleInstances, TypeOperators, ScopedTypeVariables, FlexibleContexts, GADTs #-}
module Tip.Haskell.GenericArbitrary where

import Prelude hiding (Either(..))
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen.Unsafe
import GHC.Generics as G
import Data.Typeable as T
import Control.Monad
import Data.Monoid

-- Generate a value generically.
genericArbitrary :: forall a. (T.Typeable a, QC.Arbitrary a, G.Generic a, GArbitrary (Rep a)) => QC.Gen a
genericArbitrary = QC.oneof (map gen constructors)
  where
    constructors = map (fmap to) (garbitrary (QC.arbitrary :: QC.Gen a))

-- Generating random values of a datatype
class GArbitrary f where
  -- Argument is a generator for the datatype itself, which will be used
  -- when the datatype is recursive
  garbitrary :: T.Typeable a => QC.Gen a -> [Constr (f b)]

-- Generating random constructors
class GConstr f where
  gconstructor :: T.Typeable a => QC.Gen a -> Constr (f b)

-- Represents a generator for one constructor of a datatype
data Constr a = Constr {
  -- The generator itself
  gen :: QC.Gen a,
  -- Is the constructor recursive and if so, how many times does the datatype appear
  recursion :: Int
  } deriving Functor

-- Interesting typeclass instances

instance GConstr f => GArbitrary (C1 c f) where
  -- This is the generator for a single constructor.
  -- We have to resize the "recursive generator" depending on how many
  -- times the datatype appears recursively in the constructor
  garbitrary gen = [b]
    where
      b = gconstructor (QC.sized $ \m -> QC.resize (newSize m) gen)
      newSize m
        | recursion b == 1 = m-1
        | otherwise = m `div` recursion b

instance (T.Typeable a, QC.Arbitrary a) => GConstr (K1 i a) where
  -- An argument to a constructor: see if the argument is recursive or not
  gconstructor gen =
    case gcast gen of
      Nothing ->
        -- Not recursive: use normal generator
        Constr (fmap K1 QC.arbitrary) 0
      Just gen' ->
        -- Recursive: use recursive generator
        Constr (fmap K1 gen') 1

instance (GConstr f, GConstr g) => GConstr (f :*: g) where
  -- A constructor with several arguments: add up the number of recursive occurrences
  gconstructor gen = Constr (liftM2 (:*:) g1 g2) (r1 + r2)
    where
      Constr g1 r1 = gconstructor gen
      Constr g2 r2 = gconstructor gen

-- Generic drivel that doesn't really do anything.
instance GConstr f => GConstr (M1 i c f) where
  gconstructor gen = fmap M1 (gconstructor gen)

instance GConstr U1 where
  gconstructor _ = Constr (return U1) 0

instance (GArbitrary f, GArbitrary g) => GArbitrary (f :+: g) where
  garbitrary gen = map (fmap L1) (garbitrary gen) ++ map (fmap R1) (garbitrary gen)

instance GArbitrary f => GArbitrary (D1 c f) where
  garbitrary gen = map (fmap M1) (garbitrary gen)

-- All the same but for coarbitrary. Sigh...
genericCoarbitrary :: (G.Generic a, GCoarbitrary (Rep a)) => a -> QC.Gen b -> QC.Gen b
genericCoarbitrary x = gcoarbitrary (from x)

class GCoarbitrary f where
  gcoarbitrary :: f a -> QC.Gen b -> QC.Gen b

instance (GCoarbitrary f, GCoarbitrary g) => GCoarbitrary (f :*: g) where
  gcoarbitrary (x :*: y) = gcoarbitrary x . gcoarbitrary y

instance (GCoarbitrary f, GCoarbitrary g) => GCoarbitrary (f :+: g) where
  gcoarbitrary (L1 x) = QC.variant 0 . gcoarbitrary x
  gcoarbitrary (R1 x) = QC.variant 1 . gcoarbitrary x

instance QC.CoArbitrary a => GCoarbitrary (K1 i a) where
  gcoarbitrary (K1 x) = QC.coarbitrary x

instance GCoarbitrary U1 where
  gcoarbitrary U1 = id

instance GCoarbitrary f => GCoarbitrary (M1 i c f) where
  gcoarbitrary (M1 x) = gcoarbitrary x
