-- | Calculate the call graph of a theory.
{-# LANGUAGE RecordWildCards, CPP, DeriveFunctor #-}
module Tip.CallGraph where

#include "errors.h"
import Tip.Scope
import Tip.Utils
import Tip.Core
import Tip.Pretty
import qualified Data.Map as Map
import Data.List

data Block a =
  Block {
    callers :: [Function a],
    callees :: [Function a] }
  deriving (Show, Functor)

flattenBlock :: Block a -> [Function a]
flattenBlock block = callers block ++ callees block

callGraph :: (PrettyVar a, Ord a) => Theory a -> [Block a]
callGraph thy@Theory{..} =
  [ Map.findWithDefault __ xs m | xs <- top ]
  where
    top   = topsort thy_funcs
    tops  = Map.fromList [(x, xs) | xs <- top, x <- xs]
    m     = foldl op Map.empty top
    funcs = Map.fromList [(func_name func, func) | func <- thy_funcs]
    op m xs =
      Map.insert xs (Block xs (usort ys \\ xs)) m
      where
        ys =
          concat
            [ flattenBlock (Map.findWithDefault (Block [] []) ys m)
            | x <- xs,
              y <- uses x,
              Just func <- [Map.lookup y funcs],
              Just ys   <- [Map.lookup func tops]]

data CallGraphOpts =
  CallGraphOpts {
    exploreSingleFunctions :: Bool,
    exploreCalleesFirst    :: Bool }

flatCallGraph :: (PrettyVar a, Ord a) => CallGraphOpts -> Theory a -> [[Function a]]
flatCallGraph CallGraphOpts{..} thy =
  nub . filter (not . null) $
  concat [ map callers blocks | exploreSingleFunctions ] ++ concatMap flatten blocks ++
  [concat (topsort (thy_funcs thy))]
  where
    blocks = callGraph thy
    flatten block@Block{..} =
      [ callees | exploreCalleesFirst ] ++ [flattenBlock block]
