{-# LANGUAGE ScopedTypeVariables #-}
-- | Handy utilities
module Tip.Utils where

import Data.List
import Data.Graph
import Data.List.Split
import Data.Char
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Function (on)
import Data.Ord
import Data.Function
import Control.Monad (mplus)

-- import Test.QuickCheck

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

unionOn :: Ord b => (a -> b) -> [a] -> [a] -> [a]
unionOn k = unionBy ((==) `on` k)

-- | Pair up a list with its previous elements
--
-- > withPrevious "abc" = [('a',""),('b',"a"),('c',"ab")]
withPrevious :: [a] -> [(a,[a])]
withPrevious xs = zip xs (inits xs)

-- | Binary search over a monotonic predicate
binsearch :: (Int -> Bool) -> Int -> Int -> Maybe Int
binsearch p l u
  | u < l     = Nothing
  | p m       = binsearch p l (m-1) `mplus` Just m
  | otherwise = binsearch p (m+1) u
  where
  m = (l + u) `div` 2

{-
-- | Property for 'binsearch'
prop_binsearch :: Int -> Int -> Int -> Bool
prop_binsearch l u m =
  case binsearch (>= m) l u of
    Just m' -> m' == if l > m then l else m
    Nothing -> m >= u || l > u

-- | Property for 'binsearch'
prop_binsearch_is_linsearch :: Int -> Int -> Int -> Bool
prop_binsearch_is_linsearch l u m = binsearch (>= m) l u == linsearch (>= m) l u
  where
  linsearch :: (Int -> Bool) -> Int -> Int -> Maybe Int
  linsearch p l u
    | l > u     = Nothing
    | p l       = Just l
    | otherwise = linsearch p (l+1) u
-}
