-- Select a particular conjecture from the problem.
{-# LANGUAGE RecordWildCards #-}
module Tip.Pass.SelectConjecture where

import Tip.Core
import Data.List

makeConjecture :: Int -> Theory a -> Theory a
makeConjecture n0 thy@Theory{..}
  | n < 0 || n >= length asserts = error "Assertion number out of range"
  | otherwise =
      thy {
        thy_asserts =
          proves ++
          [let u = (asserts !! n) { fm_role = Prove }
           in u { fm_body = neg (fm_body u) }
          ] ++
          take n asserts ++ drop (n+1) asserts }
  where
    (asserts, proves) = partition ((== Assert) . fm_role) thy_asserts
    n = if n0 < 0 then n0 + length asserts else n0

selectConjecture :: Int -> Theory a -> Theory a
selectConjecture n0 thy@Theory{..}
  | n < 0 || n >= length proves = error "Conjecture number out of range"
  | otherwise = thy { thy_asserts = asserts ++ [proves !! n] }
  where
    (asserts, proves) = partition ((== Assert) . fm_role) thy_asserts
    n = if n0 < 0 then n0 + length asserts else n0

provedConjecture :: Int -> Theory a -> Theory a
provedConjecture n0 thy@Theory{..}
  | n < 0 || n >= length proves = error "Conjecture number out of range"
  | otherwise =
      thy {
        thy_asserts =
          asserts ++
          [(proves !! n) { fm_role = Assert }] ++
          take n proves ++ drop (n+1) proves }
  where
    (asserts, proves) = partition ((== Assert) . fm_role) thy_asserts
    n = if n0 < 0 then n0 + length asserts else n0

deleteConjecture :: Int -> Theory a -> Theory a
deleteConjecture n0 thy@Theory{..}
  | n < 0 || n >= length proves = error "Conjecture number out of range"
  | otherwise =
      thy {
        thy_asserts =
          asserts ++
          take n proves ++ drop (n+1) proves }
  where
    (asserts, proves) = partition ((== Assert) . fm_role) thy_asserts
    n = if n0 < 0 then n0 + length asserts else n0
