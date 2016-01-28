{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.UniqLocals where

import Tip.Core
import Tip.Scope as Scope
import Tip.Fresh
import Tip.Fresh

import Control.Monad
import Control.Monad.State
import Control.Applicative

import qualified Data.Traversable as T

import qualified Data.Map as M
import qualified Data.Set as S

uniqLocals :: forall a . Name a => Theory a -> Fresh (Theory a)
uniqLocals thy
  = fmap declsToTheory
  . mapM (uniq pass_through refresh)
  . theoryDecls
  $ thy
  where
  scp       = scope thy
  nonlocals = M.keys (types scp) ++ M.keys (Scope.globals scp)
  pass_through a | a `elem` nonlocals = Just a
                 | otherwise          = Nothing

uniq :: forall a b t . (Ord a,Name b,Traversable t) => (a -> Maybe b) -> (a -> Fresh b) -> t a -> Fresh (t b)
uniq pass_through howto_fresh = flip evalStateT M.empty . T.traverse uq
  where
  uq :: a -> StateT (M.Map a b) Fresh b
  uq a =
    case pass_through a of
      Just b  -> return b
      Nothing ->
        do mb <- gets (M.lookup a)
           case mb of
             Nothing -> do b <- lift (howto_fresh a)
                           modify (M.insert a b)
                           return b
             Just b  -> do return b

