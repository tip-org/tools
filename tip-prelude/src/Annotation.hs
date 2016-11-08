{-# LANGUAGE PackageImports, NoImplicitPrelude, DeriveDataTypeable #-}
module Annotation(TipAnnotation(..), String) where

import "base" Prelude(String)
import Data.Data

data TipAnnotation =
    Name String
  | PrimitiveType
  | PrimitiveFunction
  | PrimitiveFromInteger
  | PrimitiveError
  deriving Data
