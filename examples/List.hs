module List where

import Prelude(Bool, otherwise)
import qualified Prelude
import Prelude (Bool(..),otherwise)
import Tip.DSL

{-
(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

prop_rid xs = xs ++ [] =:= xs
-}

{-
data Nat = Zero | Succ Nat

rotate :: Nat -> [a] -> [a]
rotate Zero     xs     = xs
rotate (Succ n) []     = []
rotate (Succ n) (x:xs) = rotate n (xs ++ [x])

length :: [a] -> Nat
length []     = Zero
length (_:xs) = Succ (length xs)

prop_rotate xs = rotate (length xs) xs =:= xs
-}

{-
filter :: (a -> Bool) -> [a] -> [a]
filter p (x:xs) | p x       = x:filter p xs
                | otherwise = filter p xs
filter p [] = []
-}

bap :: (a -> b) -> [a] -> [b]
bap f (x:xs) = f x:bap f xs
bap f []     = []

map :: (a -> b) -> [a] -> [b]
map g (a:as) = g a:map g as
map h []     = []

zap :: (a -> b) -> [a] -> [b]
zap u []     = []
zap u (l:ls) = u l:zap u ls

{-# NOINLINE (.) #-}
f . g = \ x -> f (g x)

{-# NOINLINE dot #-}
(a `dot` b) c = a (b c)

map_compose f g = bap f `dot` map g =:= zap (f . g)

