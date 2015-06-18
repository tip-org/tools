{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Fresh monad and the Name type class
module Tip.Fresh where

import Tip.Utils
import Tip.Pretty
import Control.Applicative hiding (empty)
import Control.Monad.State.Strict
import Control.Arrow ((&&&))

import Data.Foldable (Foldable)

-- | The Fresh monad
newtype Fresh a = Fresh (State Int a)
  deriving (Monad, Applicative, Functor, MonadFix)

-- | Continues making unique names after the highest
--   numbered name in a foldable value.
freshPass :: (Foldable f,Name a) => (f a -> Fresh b) -> f a -> b
f `freshPass` x = f x `freshFrom` x

-- | Run fresh from starting from the greatest unique in a structure
freshFrom :: (Foldable f,Name b) => Fresh a -> f b -> a
freshFrom m x = runFreshFrom (succ (maximumOn getUnique x)) m

-- | Run fresh, starting from zero
runFresh :: Fresh a -> a
runFresh (Fresh m) = evalState m 0

-- | Run fresh from some starting value
runFreshFrom :: Int -> Fresh a -> a
runFreshFrom n (Fresh m) = evalState m (n+1)

-- | The Name type class
class (PrettyVar a, Ord a) => Name a where
  -- | Make a fresh name
  fresh   :: Fresh a

  -- | Refresh a name, which could have some resemblance to the original
  -- name
  refresh :: a -> Fresh a
  refresh _ = fresh

  -- | Make a fresh name that can incorporate the given string
  freshNamed :: String -> Fresh a
  freshNamed _ = fresh

  -- | Refresh a name with an additional hint string
  refreshNamed :: String -> a -> Fresh a
  refreshNamed s n = freshNamed (s ++ varStr n)

  -- | Gets the unique associated with a name.
  getUnique :: a -> Int

instance Name Int where
  fresh     = Fresh (state (id &&& succ))
  getUnique = id

instance Name a => Name (PPVar a) where
  fresh = fmap PPVar fresh
  refresh = fmap PPVar . refresh . unPPVar
  freshNamed = fmap PPVar . freshNamed
  refreshNamed s n = fmap PPVar (refreshNamed s (unPPVar n))

