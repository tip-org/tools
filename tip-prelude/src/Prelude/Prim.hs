{-# LANGUAGE MagicHash, NoImplicitPrelude, PackageImports #-}
module Prelude.Prim where

import "base" Prelude(Bool(..))
import GHC.Prim
import Tip.GHC.Annotations
import Unsafe.Coerce

{-# ANN special Special #-}
{-# NOINLINE special #-}
special :: Addr# -> a
special name = unsafeCoerce ()

{-# ANN type Integer (PrimType Integer) #-}
data Integer = MkInteger Integer

{-# ANN type Rational (PrimType Real) #-}
data Rational = MkRational Rational

{-# ANN primEquals Inline #-}
primEquals :: a -> a -> Bool
primEquals = special "Primitive Equal 2"#
    
{-# ANN primDistinct Inline #-}
primDistinct :: a -> a -> Bool
primDistinct = special "Primitive Distinct 2"#
    
{-# ANN primLe Inline #-}
primLe :: a -> a -> Bool
primLe = special "Primitive NumLe 2"#
    
{-# ANN primGe Inline #-}
primGe :: a -> a -> Bool
primGe = special "Primitive NumGe 2"#
    
{-# ANN primLt Inline #-}
primLt :: a -> a -> Bool
primLt = special "Primitive NumLt 2"#
    
{-# ANN primGt Inline #-}
primGt :: a -> a -> Bool
primGt = special "Primitive NumGt 2"#

{-# ANN primPlus Inline #-}
primPlus :: a -> a -> a
primPlus = special "Primitive NumAdd 2"#

{-# ANN primMinus Inline #-}
primMinus :: a -> a -> a
primMinus = special "Primitive NumSub 2"#

{-# ANN primTimes Inline #-}
primTimes :: a -> a -> a
primTimes = special "Primitive NumMul 2"#

{-# ANN primDiv Inline #-}
primDiv :: a -> a -> a
primDiv = special "Primitive IntDiv 2"#

{-# ANN primMod Inline #-}
primMod :: a -> a -> a
primMod = special "Primitive IntMod 2"#

{-# ANN primCast Inline #-}
primCast :: a -> b
primCast = special "Cast"#

{-# ANN primQuotient Inline #-}
primQuotient :: a -> a -> a
primQuotient = special "Primitive NumDiv 2"#

{-# ANN primAnd Inline #-}
primAnd :: Bool -> Bool -> Bool
primAnd = special "Primitive And 2"#

{-# ANN primOr Inline #-}
primOr :: Bool -> Bool -> Bool
primOr = special "Primitive Or 2"#

{-# ANN primNot Inline #-}
primNot :: Bool -> Bool
primNot = special "Primitive Not 1"#

{-# ANN primError Inline #-}
primError :: a
primError = special "Error"#
