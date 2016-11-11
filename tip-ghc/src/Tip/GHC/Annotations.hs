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
  | PrimType BuiltinType | SomeSpecial Special | Special | Literal Lit
    -- The type of properties.
  | PropType
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
    -- The constructor for rational numbers (type integer -> integer -> real).
  | Rational
  deriving (Eq, Ord, Show, Read, Data)
