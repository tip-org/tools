module List where

import qualified Prelude
import Prelude (Bool(..),otherwise)
import Tip.DSL

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

prop_rid xs = xs ++ [] =:= xs

map :: (a -> b) -> [a] -> [b]
map f (x:xs) = f x:map f xs
map f []     = []

filter :: (a -> Bool) -> [a] -> [a]
filter p (x:xs) | p x       = x:filter p xs
                | otherwise = filter p xs
filter p [] = []

{-# NOINLINE (.) #-}
f . g = \ x -> f (g x)

f `dot` g = \ x -> f (g x)

map_compose f g = map f . map g =:= map (f . g)

map_compose2 f g = map f `dot` map g =:= map (f `dot` g)
