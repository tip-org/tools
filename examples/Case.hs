module List where

import Prelude(Bool, otherwise)
import qualified Prelude
import Prelude (Bool(..),otherwise, id, ($), (.))
import Tip

map f xs = [ f x | x <- xs ]

prop_mc f g = map (f . g) === map f . map g


filter :: (a -> Bool) -> [a] -> [a]
filter p (x:xs) = case p x of { True -> (x:); False -> id } $ filter p xs
filter p []     = []

prop_filter p = filter (p . p) === filter p

mf :: (a -> a) -> (a -> Bool) -> [a] -> [a]
mf f p (x:xs) = f x:mf (if p x then f . f else f) p xs
mf f p []     = []

prop_mf f p = mf f (p . p) === mf f p

prop_bla a b c d e f = (if (if a then b else c) then d else e) === f
