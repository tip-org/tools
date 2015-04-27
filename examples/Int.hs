module Int where

import Tip.DSL

i :: Int -> Int
i 0 = 0
i y = i (y-1)

g,f,h,z :: Int -> Int -> Int
g x y = x
f a b = a
h i j = j
z p q = h p q

prop_abc = g (f (h (z 0 1) 2) 3) 4 =:= (2 :: Int)

prop_int :: Int -> Prop Int
prop_int x = i x + x =:= 1

prop_int2 :: Int -> Prop Bool
prop_int2 x = i x > x =:= i x < x

apa :: Int -> [Int]
apa 0 = []
apa n = n:apa (n-1)

prop_apa n = [] =:= apa n

prop_div_mod :: Int -> Prop Int
prop_div_mod x = x `div` 2 =:= x `mod` 2
