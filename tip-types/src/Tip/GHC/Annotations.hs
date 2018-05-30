{-# LANGUAGE DeriveDataTypeable #-}
module Tip.GHC.Annotations(
  module Tip.GHC.Annotations,
  BuiltinType(..), Builtin(..), Lit(..)) where

import Data.Data
import Tip.Types

-- An annotation that can be attached to a function to give it special
-- meaning in tip-ghc.
data TipAnnotation =
    -- Rename the function when translating it to TIP.
    Name String
    -- Rename the projection functions for this constructor.
  | Projections [String]
    -- Unconditionally inline the function
    -- (useful when the function must be applied to a monomorphic type).
  | Inline
    -- TIP built-in types, special functions and literals.
  | PrimType BuiltinType | SomeSpecial Special
  | MakeWiredIn WiredIn | WiredIn WiredIn | Special | Literal Lit
    -- The type of properties.
  | PropType
    -- Give an attribute to the function
  | Attribute String (Maybe String)
  deriving (Eq, Ord, Show, Data)

-- Special functions which tip-ghc knows about.
data Special =
    -- A TIP builtin. The second argument is the arity.
    Primitive Builtin Int
    -- An error function.
  | Error
    -- Cast between two types, which should either
    --   a) have the same representation in TIP, or
    --   b) be a cast from integer to real.
  | Cast
    -- The magic inlining function inline :: a -> a.
  | InlineIt
    -- A quantifier.
  | QuantSpecial Quant
  deriving (Eq, Ord, Show, Read, Data)

-- Functions which are invoked by tip-ghc and must be defined
-- in the prelude.
data WiredIn =
    -- Convert a pair of integers to a rational.
    MakeRational
    -- Negate a number.
  | Negate
  deriving (Eq, Ord, Show, Read, Data)
