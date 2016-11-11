{-# LANGUAGE MagicHash, NoImplicitPrelude, PackageImports #-}
module Tip(module Tip, module Tip.GHC.Annotations) where

import Tip.GHC.Annotations
import Prelude.Prim
import qualified "base" Prelude

{-# ANN type Prop PropType #-}
{-# ANN type Prop (PrimType Boolean) #-}
data Prop = MkProp Prop

(===) :: Prelude.Eq a => a -> a -> Prop
(===) = special "Primitive Equal 2"#

{-# ANN inline (SomeSpecial InlineIt) #-}
{-# NOINLINE inline #-}
inline :: a -> a
inline x = x
