module Tip.Utils where

import Data.List
import Data.Graph

-- | Sort and remove duplicates
usort :: Ord a => [a] -> [a]
usort = map head . group . sort

-- | Sort things in topologically in strongly connected components
sortThings :: Ord name => (thing -> name) -> (thing -> [name]) -> [thing] -> [[thing]]
sortThings name refers things =
    map flattenSCC $ stronglyConnComp
        [ (thing,name thing,filter (`elem` names) (refers thing))
        | thing <- things
        ]
  where
    names = map name things
