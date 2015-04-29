module Tip.Utils where

import Data.List

-- | Sort and remove duplicates
usort :: Ord a => [a] -> [a]
usort = map head . group . sort
