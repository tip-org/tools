-- A faster implementation of the writer monad.

{-# LANGUAGE Rank2Types #-}
module Tip.Writer where

import Data.Monoid

import Control.Monad
import Control.Applicative

newtype WriterT w m a = WriterT { unWriterT :: forall b. (w -> a -> m b) -> m b }

instance (Monoid w, Monad m) => Functor (WriterT w m) where
  {-# INLINE fmap #-}
  fmap f x = x >>= return . f

instance (Monoid w, Monad m) => Applicative (WriterT w m) where
  {-# INLINE pure #-}
  pure = return
  {-# INLINE (<*>) #-}
  (<*>) = liftM2 ($)

instance (Monoid w, Monad m) => Monad (WriterT w m) where
  {-# INLINE return #-}
  return x = WriterT (\k -> k mempty x)

  {-# INLINE (>>=) #-}
  WriterT m >>= f =
    WriterT $ \k ->
      m (\w x -> unWriterT (f x) (\w' y -> k (w `mappend` w') y))

{-# INLINE runWriterT #-}
runWriterT :: (Monoid w, Monad m) => WriterT w m a -> m (a, w)
runWriterT (WriterT f) = f (\w x -> return (x, w))

{-# INLINE tell #-}
tell :: (Monoid w, Monad m) => w -> WriterT w m ()
tell w = WriterT (\k -> k w ())

{-# INLINE lift #-}
lift :: (Monoid w, Monad m) => m a -> WriterT w m a
lift x = WriterT (\k -> x >>= \y -> k mempty y)

{-# INLINE censor #-}
censor :: (Monoid w, Monad m) => (w -> w) -> WriterT w m a -> WriterT w m a
censor f (WriterT m) = WriterT (\k -> m (\w x -> k (f w) x))
