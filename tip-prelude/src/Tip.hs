{-# LANGUAGE MagicHash, NoImplicitPrelude, PackageImports, TypeOperators #-}
module Tip(module Tip, module Tip.GHC.Annotations) where

import Tip.GHC.Annotations(TipAnnotation(Name, Projections, Inline, Source, Attr, AttrValue))
import qualified Tip.GHC.Annotations as Annotations
import Prelude.Prim
import qualified "base" Prelude

infix 3 ===
infix 3 =/=
infixr 2 .&&.
infixr 1 .||.
infixr 0 ==>

{-# ANN type Property Annotations.PropType #-}
{-# ANN type Property (Annotations.PrimType Annotations.Boolean) #-}
data Property = MkProp Property

type Equality a = Property
type a :=>: b = Property
type And a b = Property
type Or a b = Property
type Neg a = Property
type Forall a b = Property
type Exists a b = Property

class Testable a where
instance Testable Prelude.Bool
instance Testable Property

{-# ANN property Inline #-}
property :: Testable prop => prop -> Property
property = special "Cast"#

{-# ANN bool Inline #-}
bool :: Prelude.Bool -> Property
bool = special "Cast"#

{-# ANN (===) Inline #-}
(===) :: a -> a -> Property
(===) = special "Primitive Equal 2"#

{-# ANN (=/=) Inline #-}
(=/=) :: a -> a -> Property
(=/=) = special "Primitive Distinct 2"#

{-# ANN (.&&.) Inline #-}
(.&&.) :: (Testable p, Testable q) => p -> q -> Property
(.&&.) = special "Primitive And 2"#

{-# ANN (.||.) Inline #-}
(.||.) :: (Testable p, Testable q) => p -> q -> Property
(.||.) = special "Primitive Or 2"#

{-# ANN (==>) Inline #-}
(==>) :: (Testable p, Testable q) => p -> q -> Property
(==>) = special "Primitive Implies 2"#

{-# ANN neg Inline #-}
neg :: Testable prop => prop -> Property
neg = special "Primitive Not 1"#

{-# ANN question Inline #-}
question :: Testable prop => prop -> Property
question = neg

{-# ANN forAll Inline #-}
forAll :: Testable prop => (a -> prop) -> Property
forAll = special "QuantSpecial Forall"#

{-# ANN exists Inline #-}
exists :: Testable prop => (a -> prop) -> Property
exists = special "QuantSpecial Exists"#

{-# ANN inline (Annotations.SomeSpecial Annotations.InlineIt) #-}
{-# NOINLINE inline #-}
inline :: a -> a
inline x = x
