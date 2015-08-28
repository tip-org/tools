{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
-- | Handy utilities
module Tip.Utils where

import Data.List
import Data.Maybe
import Data.Graph hiding (components)
import Data.List.Split
import Data.Char
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Function (on)
import Data.Ord
import Data.Function

-- | Sort and remove duplicates
usort :: Ord a => [a] -> [a]
usort = usortOn id

-- | Sort and remove duplicates wrt some custom ordering
usortOn :: Ord b => (a -> b) -> [a] -> [a]
usortOn f = map head . groupBy ((==) `on` f) . sortBy (comparing f)

-- | Union on a predicate
unionOn :: Ord b => (a -> b) -> [a] -> [a] -> [a]
unionOn k = unionBy ((==) `on` k)

-- | Returns the duplicates in a list
duplicates :: Ord a => [a] -> [a]
duplicates xs = usort [ x | x <- xs, count x > 1 ]
  where count x = length (filter (== x) xs)

data Component a = Rec [a] | NonRec a
  deriving (Eq,Ord,Show,Functor)

flattenComponent :: Component a -> [a]
flattenComponent (Rec xs) = xs
flattenComponent (NonRec x) = [x]

-- | Strongly connected components
components :: Ord name => (thing -> name) -> (thing -> [name]) -> [thing] -> [Component thing]
components name refers things =
    [ case comp of
        [(thing,n,refs)]
          | n `notElem` refs -> NonRec thing
        _                    -> Rec [ thing | (thing,_,_) <- comp ]
    | comp <- map flattenSCC $ stronglyConnCompR
        [ (thing,name thing,filter (`elem` names) (refers thing))
        | thing <- things
        ]
    ]
  where
  names = map name things

lookupComponent :: Eq thing => thing -> [Component thing] -> Maybe (Component thing)
lookupComponent x = listToMaybe . mapMaybe h
  where
  h c = case c of NonRec y | x == y      -> Just c
                  Rec ys   | x `elem` ys -> Just c
                  _ -> Nothing

-- | Sort things in topologically in strongly connected components
sortThings :: Ord name => (thing -> name) -> (thing -> [name]) -> [thing] -> [[thing]]
sortThings name refers things = map flattenComponent (components name refers things)

-- | Recursive
recursive :: Ord name => (thing -> name) -> (thing -> [name]) -> [thing] -> [name]
recursive name refers things =
  [ name x | Rec xs <- components name refers things, x <- xs ]

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
maximumOn :: forall f a b . (F.Foldable f,Ord b) => (a -> b) -> f a -> b
maximumOn f = f . F.maximumBy (comparing f)

-- | Pair up a list with its previous elements
--
-- > withPrevious "abc" = [('a',""),('b',"a"),('c',"ab")]
withPrevious :: [a] -> [(a,[a])]
withPrevious xs = zip xs (inits xs)

-- | Cursored traversal with previous and next elements of a list
cursor :: [a] -> [([a],a,[a])]
cursor xs = [ let (l,x:r) = splitAt i xs in (l,x,r) | i <- [0..length xs-1] ]

