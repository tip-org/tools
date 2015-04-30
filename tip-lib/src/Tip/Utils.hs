-- | Handy utilities
module Tip.Utils where

import Data.List
import Data.Graph
import Data.List.Split
import Data.Char

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

-- | Makes a nice flag from a constructor string
--
-- > > flagify "PrintPolyFOL"
-- > "print-poly-fol"
flagify :: String -> String
flagify
    = map toLower . intercalate "-"
    . split (condense $ dropInitBlank $ keepDelimsL $ whenElt (\x -> isUpper x || isSpace x))

-- | Makes a flag from something @Show@-able
flagifyShow :: Show a => a -> String
flagifyShow = flagify . show

