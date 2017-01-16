{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
module Tip.Pass.DropSuffix where

import Tip.Pretty
import Tip.Fresh
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.State

dropSuffix :: forall f a . (Traversable f,Name a) => String -> f a -> Fresh (f a)
dropSuffix suf thy = evalStateT (traverse f thy) M.empty
  where
    f :: a -> StateT (Map a a) Fresh a
    f x
      | (pre,_:_) <- break (`elem` suf) (varStr x)
      = do m <- get
           case M.lookup x m of
             Just y  -> return y
             Nothing -> do y <- lift (freshNamed pre)
                           modify (M.insert x y)
                           return y
    f x = return x

