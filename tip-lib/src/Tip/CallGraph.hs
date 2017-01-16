-- | Calculate the call graph of a theory.
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards, CPP, DeriveFunctor #-}
module Tip.CallGraph where

#include "errors.h"
import Tip.Utils
import Tip.Core
import Tip.Pretty
import qualified Data.Map as Map
import Data.List

type FS = Function :+: Signature

data Block a =
  Block {
    callers :: [FS a],
    callees :: [FS a] }
  deriving (Show, Functor)

flattenBlock :: Block a -> [FS a]
flattenBlock block = callers block ++ callees block

theoryStuff :: Theory a -> [FS a]
theoryStuff Theory{..} = map InL thy_funcs ++ map InR thy_sigs

callGraph :: (PrettyVar a, Ord a) => Theory a -> [Block a]
callGraph thy@Theory{..} =
  [ Map.findWithDefault __ xs m | xs <- top ]
  where
    stuff = theoryStuff thy
    top   = topsort stuff
    tops  = Map.fromList [(x, xs) | xs <- top, x <- xs]
    m     = foldl op Map.empty top
    funcs = Map.fromList [(defines func, func) | func <- stuff]
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

flatCallGraph :: (PrettyVar a, Ord a) => CallGraphOpts -> Theory a -> [[FS a]]
flatCallGraph CallGraphOpts{..} thy =
  nub . filter (not . null) $
  concat [ map callers blocks | exploreSingleFunctions ] ++ concatMap flatten blocks ++
  [concat (topsort (theoryStuff thy))]
  where
    blocks = callGraph thy
    flatten block@Block{..} =
      [ callees | exploreCalleesFirst ] ++ [flattenBlock block]
