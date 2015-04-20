{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Tip.Fresh where

import Tip.Pretty
import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Arrow ((&&&))

newtype Fresh a = Fresh (State Int a)
  deriving (Monad, Applicative, Functor, MonadFix)

class (PrettyVar a, Ord a) => Name a where
  fresh   :: Fresh a

  refresh :: a -> Fresh a
  refresh _ = fresh

  freshNamed :: String -> Fresh a
  freshNamed _ = fresh

  refreshNamed :: String -> a -> Fresh a
  refreshNamed s n = freshNamed (s ++ varStr n)

  getUnique :: a -> Int

mkTyVarName :: Int -> String
mkTyVarName x = vars !! x
  where vars = ["a","b","c","d"] ++ ["t" ++ show i | i <- [0..]]


instance Name Int where
  fresh     = Fresh (state (id &&& succ))
  getUnique = id

runFresh :: Fresh a -> a
runFresh (Fresh m) = evalState m 0

runFreshFrom :: Int -> Fresh a -> a
runFreshFrom n (Fresh m) = evalState m (n+1)

