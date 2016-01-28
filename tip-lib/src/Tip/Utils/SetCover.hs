{-# LANGUAGE ScopedTypeVariables #-}
-- | Set covers
module Tip.Utils.SetCover (cover, covers) where

import MiniSat

import Data.Map (Map)
import qualified Data.Map as M

import System.IO.Unsafe

import Data.List

import Tip.Utils (usort)

-- | Finds all minimal covers
covers :: forall o a . Ord a => [(o,[a])] -> [[o]]
covers objs = map (map (m M.!)) sol
  where
  (os,as) = unzip objs
  sol :: [[Int]]
  sol = covers' ([0..] `zip` as)
  m   :: Map Int o
  m   = M.fromList ([0..] `zip` os)

covers' :: forall o a . (Ord o,Ord a) => [(o,[a])] -> [[o]]
covers' objs =
  map sort $ sort $
  unsafePerformIO $
  withNewSolver $ \ s ->
    do lobjs <-
         sequence
           [ do ol <- newLit s
                return (o,ol,as)
           | (o,as) <- objs
           ]
       sequence_
         [ addClause s [ ol | (o,ol,as) <- lobjs , p `elem` as ]
         | p <- usort (concat [ as | (_,as) <- objs ])
         ]
       let loop =
             do b <- solve s []
                if b then step else return []

           step =
             do model <-
                  sequence
                    [ do v <- modelValue s ol
                         return (v,(ol,o),as)
                    | (o,ol,as) <- lobjs
                    ]
                let mini = cover [ (olo,as) | (Just True,olo,as) <- model ]
                addClause s [ neg ol | (ol,_) <- mini ]
                fmap ([ o | (_,o) <- mini ]:) loop
       loop

-- | Finds one minimal cover
cover :: forall a o . Ord a => [(o,[a])] -> [o]
cover xs =
  let occs = M.fromListWith (+) [ (a,1) | (_,as) <- xs, a <- as ]
  in  case shrink occs xs of
        (True,xs') -> cover xs'
        (False,_)  -> map fst xs
  where
  shrink :: Map a Int -> [(o,[a])] -> (Bool,[(o,[a])])
  shrink _ []          = (False,[])
  shrink m ((o,as):xs)
    | and [ M.findWithDefault 0 a m > 1 | a <- as ]
    = success (shrink (foldr (M.adjust pred) m as) xs)
    | otherwise
    = fmap ((o,as):) (shrink m xs)

  success (_,r) = (True,r)

