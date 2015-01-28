{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Fresh where

import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Arrow ((&&&))

newtype Fresh a = Fresh { dirty :: State Int a }
  deriving (Monad, Applicative, Functor, MonadFix)

class Fresh a where
  fresh   :: Fresh a

  refresh :: a -> Fresh a
  refresh _ = fresh

instance Fresh Int where
  fresh = Fresh (state (id &&& succ))

runFresh :: FreshM a -> a
runFresh (FreshM m) = evalState m 0

runFreshFrom :: Int -> FreshM a -> a
runFreshFrom n (FreshM m) = evalState m n

