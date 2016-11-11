{-# LANGUAGE MagicHash #-}
module Tip(module Tip, module Tip.GHC.Annotations) where

import Tip.GHC.Annotations
import Prelude.Prim

{-# ANN type Prop PropType #-}
{-# ANN type Prop (PrimType Boolean) #-}
data Prop = MkProp Prop

(===) :: Eq a => a -> a -> Prop
(===) = special "Primitive Equal 2"#
