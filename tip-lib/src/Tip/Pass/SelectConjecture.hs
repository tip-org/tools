-- Select a particular conjecture from the problem.
{-# LANGUAGE RecordWildCards #-}
module Tip.Pass.SelectConjecture where

import Tip.Core
import Data.List

selectConjecture :: Int -> Theory a -> Theory a
selectConjecture n thy@Theory{..}
  | n < 0 || n >= length proves = error "Conjecture number out of range"
  | otherwise = thy { thy_asserts = asserts ++ [proves !! n] }
  where
    (asserts, proves) = partition ((== Assert) . fm_role) thy_asserts

provedConjecture :: Int -> Theory a -> Theory a
provedConjecture n thy@Theory{..}
  | n < 0 || n >= length proves = error "Conjecture number out of range"
  | otherwise =
      thy {
        thy_asserts =
          asserts ++
          [(proves !! n) { fm_role = Assert }] ++
          take n proves ++ drop (n+1) proves }
  where
    (asserts, proves) = partition ((== Assert) . fm_role) thy_asserts
