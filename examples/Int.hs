module Int where

import Tip.DSL

bloopl True = False
bloopl False = True

i :: Int -> Int
i 0 = 0
i 1 = 1
i 3 = 5
i y | y == 2 = 8
i y = i (y-1)

{-
g,f,h,z :: Int -> Int -> Int
g x y = x
f a b = a
h i j = j
z p q = h p q

prop_abc = g (f (h (z 0 1) 2) 3) 4 =:= (2 :: Int)
-}

prop_int :: Int -> Prop Int
prop_int x = i x + x =:= 1

prop_int2 :: Int -> Prop Bool
prop_int2 x = i x > x =:= i x < x

propbloopl b = bloopl b =:= not b
