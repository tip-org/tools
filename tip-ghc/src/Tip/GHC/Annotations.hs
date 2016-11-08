{-# LANGUAGE DeriveDataTypeable #-}
module Tip.GHC.Annotations where

import Data.Data

-- An annotation that can be attached to a function to give it special
-- meaning in tip-ghc.
data TipAnnotation =
    -- Rename the function when translating it to TIP.
    Name String
    -- Rename the projection functions for this constructor.
  | Projections [String]
    -- TIP built-in types, functions and literals.
  | PrimType String | Primitive | Literal String
    -- The type of properties.
  | PropType
    -- The fromInteger and fromRational functions.
  | FromInteger | FromRational
  deriving (Eq, Ord, Show, Data)
