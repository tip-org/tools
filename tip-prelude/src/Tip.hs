{-# LANGUAGE MagicHash, NoImplicitPrelude, PackageImports #-}
module Tip(module Tip, module Tip.GHC.Annotations) where

import Tip.GHC.Annotations
import Prelude.Prim
import qualified "base" Prelude

infix 3 ===
infix 3 =/=
infixr 2 .&&.
infixr 1 .||.
infixr 0 ==>

{-# ANN type Prop PropType #-}
{-# ANN type Prop (PrimType Boolean) #-}
data Prop = MkProp Prop

{-# ANN bool Inline #-}
bool :: Prelude.Bool -> Prop
bool = special "Cast"#

{-# ANN (===) Inline #-}
(===) :: Prelude.Eq a => a -> a -> Prop
(===) = special "Primitive Equal 2"#

{-# ANN (=/=) Inline #-}
(=/=) :: Prelude.Eq a => a -> a -> Prop
(=/=) = special "Primitive Distinct 2"#

{-# ANN (.&&.) Inline #-}
(.&&.) :: Prop -> Prop -> Prop
(.&&.) = special "Primitive And 2"#

{-# ANN (.||.) Inline #-}
(.||.) :: Prop -> Prop -> Prop
(.||.) = special "Primitive Or 2"#

{-# ANN (==>) Inline #-}
(==>) :: Prop -> Prop -> Prop
(==>) = special "Primitive Implies 2"#

{-# ANN neg Inline #-}
neg :: Prop -> Prop
neg = special "Primitive Not 1"#

{-# ANN question Inline #-}
question :: Prop -> Prop
question = neg

{-# ANN forAll Inline #-}
forAll :: (a -> Prop) -> Prop
forAll = special "QuantSpecial ForAll"#

{-# ANN exists Inline #-}
exists :: (a -> Prop) -> Prop
exists = special "QuantSpecial Exists"#

{-# ANN inline (SomeSpecial InlineIt) #-}
{-# NOINLINE inline #-}
inline :: a -> a
inline x = x
