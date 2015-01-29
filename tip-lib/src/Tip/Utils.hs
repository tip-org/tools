module Tip.Utils where

import Data.List

usort :: Ord a => [a] -> [a]
usort = map head . group . sort
