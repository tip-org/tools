{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
module Tip.EqualFunctions(collapseEqual) where

import Tip
import Tip.Fresh

import Data.Traversable
import Data.Generics.Geniplate
import Control.Applicative
import Data.Either
import Data.List (delete, inits)

renameVars :: Traversable f => (a -> Bool) -> f a -> f (Either a Int)
renameVars is_var t = runFresh (traverse rename t)
  where
    rename x | is_var x = Right <$> fresh
    rename x = return (Left x)

renameFn :: Ord a => Function a -> Function (Either a Int)
renameFn fn = renameVars (`notElem` gbls) fn
  where
    gbls = delete (func_name fn) (globals fn)

-- If we have
--   f x = E[x]
--   g y = E[y]
-- then we remove g and replace it with f everywhere
collapseEqual :: forall a . Ord a => Theory a -> Theory a
collapseEqual thy@(Theory{thy_func_decls=fns0})
    = fmap rename (thy{thy_func_decls=survivors})
  where
    rfs :: [(Function a,Function (Either a Int))]
    rfs = [ (f,renameFn f) | f <- fns0 ]

    renamings :: [(a,a)]
    survivors :: [Function a]
    (renamings,survivors) = partitionEithers
        [ case [ (func_name f,func_name g) | (g,rg) <- prev , rf == rg ] of
            []   -> Right f -- f is better
            fg:_ -> Left fg -- g is better
        | ((f,rf),prev) <- withPrevious rfs
        ]

    rename :: a -> a
    rename x = case lookup x renamings of
        Just y  -> y
        Nothing -> x

-- | Pair up a list with its previous elements
--
-- > withPrevious "abc" = [('a',""),('b',"a"),('c',"ab")]
withPrevious :: [a] -> [(a,[a])]
withPrevious xs = zip xs (inits xs)

