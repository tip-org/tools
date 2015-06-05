-- Very bad dead code elimination (doesn't detect dead recursive functions).

{-# LANGUAGE RecordWildCards #-}
module Tip.Pass.EliminateDeadCode where

import Tip.Core
import qualified Data.Set as Set
import Data.Generics.Geniplate

eliminateDeadCode :: Ord a => Theory a -> Theory a
eliminateDeadCode = fixpoint elim
  where
    elim thy@Theory{..} =
      thy {
        thy_sigs = filter (flip Set.member alive . sig_name) thy_sigs,
        thy_funcs = filter (flip Set.member alive . func_name) thy_funcs }
      where
        alive = Set.fromList (map gbl_name (universeBi thy))

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x
  | x == y = x
  | otherwise = fixpoint f y
  where
    y = f x
