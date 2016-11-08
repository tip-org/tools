{-# LANGUAGE PackageImports, MagicHash #-}
module Prelude(module Prelude, P.String, module Tip.GHC.Annotations) where

import qualified "base" Prelude as P
import qualified Data.Ratio as P
import "base" Prelude(Bool(False, True))
import GHC.Prim
import Tip.GHC.Annotations
import Unsafe.Coerce

-- XXX more fixity
infixr 5  ++

{-# ANN primitive Primitive #-}
{-# NOINLINE primitive #-}
primitive :: Addr# -> Int# -> a
primitive name arity = unsafeCoerce ()

{-# ANN type Int (PrimType "Integer") #-}
data Int = MkInt Int
type Integer = Int

not :: Bool -> Bool
not = primitive "Not"# 1#

class Eq a where

instance Eq Int
instance Eq Float

instance Eq a => Eq [a]

(==) :: Eq a => a -> a -> Bool
(==) = primitive "Equal"# 2#

(/=) :: Eq a => a -> a -> Bool
x /= y = primitive "Distinct"# 2#

{-# ANN type Prop PropType #-}
{-# ANN type Prop (PrimType "Boolean") #-}
data Prop = MkProp Prop

(===) :: Eq a => a -> a -> Prop
(===) = primitive "Equal"# 2#

class Num a where
instance Num Int
instance Num Float

(+) :: Num a => a -> a -> a
(+) = primitive "NumAdd"# 2#

(&&) :: Bool -> Bool -> Bool
(&&) = primitive "And"# 2#

{-# ANN type Float (PrimType "Real") #-}
data Float = MkFloat Float
type Double = Float

{-# ANN fromInteger FromInteger #-}
{-# NOINLINE fromInteger #-}
fromInteger :: Num a => P.Integer -> a
fromInteger x = unsafeCoerce ()

{-# ANN fromRational FromRational #-}
{-# NOINLINE fromRational #-}
fromRational :: Num a => P.Rational -> a
fromRational x = unsafeCoerce ()

(/) :: Num a => a -> a -> a
(/) = primitive "NumDiv"# 2#

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)
