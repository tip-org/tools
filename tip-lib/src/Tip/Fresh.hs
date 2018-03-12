{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Fresh monad and the Name type class
module Tip.Fresh where

import Tip.Utils
import Tip.Pretty
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

-- | Run fresh from some starting value
runFreshFrom :: Int -> Fresh a -> a
runFreshFrom n (Fresh m) = evalState m (n+1)

-- | The Name type class
class (PrettyVar a, Ord a) => Name a where
  -- | Make a fresh name that can incorporate the given string
  freshNamed :: String -> Fresh a

  -- | Gets the unique associated with a name.
  -- May return 0 if the name was not generated using 'freshNamed'.
  getUnique :: a -> Int

-- | Make a fresh name
fresh :: Name a => Fresh a
fresh = freshNamed ""

-- | Refresh a name, which could have some resemblance to the original
-- name
refresh :: (PrettyVar a, Name b) => a -> Fresh b
refresh x = freshNamed (varStr x)

-- | Refresh a name, adding a prefix to it
refreshNamed :: (PrettyVar a, Name b) => String -> a -> Fresh b
refreshNamed prefix x = freshNamed (prefix ++ "-" ++ varStr x)

instance Name Int where
  freshNamed _ = Fresh (state (id &&& succ))
  getUnique = id

instance Name a => Name (PPVar a) where
  freshNamed = fmap PPVar . freshNamed
  getUnique = getUnique . unPPVar

