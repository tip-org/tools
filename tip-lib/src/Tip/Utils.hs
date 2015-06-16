{-# LANGUAGE ScopedTypeVariables #-}
-- | Handy utilities
module Tip.Utils where

import Data.List
import Data.Graph
import Data.List.Split
import Data.Char
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Ord
import Data.Function

-- | Sort and remove duplicates
usort :: Ord a => [a] -> [a]
usort = usortOn id

-- | Sort and remove duplicates wrt some custom ordering
usortOn :: Ord b => (a -> b) -> [a] -> [a]
usortOn f = map head . groupBy ((==) `on` f) . sortBy (comparing f)

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

-- | Calculates the maximum value of a foldable value.
--
-- Useful to find the highest unique in a structure
maximumOn :: forall f a b . (F.Foldable f,Ord b) => (a -> b) -> f a -> b
maximumOn f = f . F.maximumBy (comparing f)

