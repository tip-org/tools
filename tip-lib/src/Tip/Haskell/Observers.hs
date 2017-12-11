module Tip.Haskell.Observers where

import Test.QuickCheck

mkObserve :: (Int -> a -> b) -> a -> Gen b
mkObserve f t = do
  n <- arbitrary
  return (f n t)
