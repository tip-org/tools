{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.UniqLocals where

import Tip.Core
import Tip.Scope as Scope
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
  . mapM (flip evalStateT M.empty . T.traverse uq)
  . theoryDecls
  $ thy
  where
  nonlocals = M.keys (types scp) ++ M.keys (Scope.globals scp)
  scp       = scope thy
  uq :: a -> StateT (M.Map a a) Fresh a
  uq a | a `elem` nonlocals = do return a
       | otherwise          = do mb <- gets (M.lookup a)
                                 case mb of
                                   Nothing -> do b <- lift (refresh a)
                                                 modify (M.insert a b)
                                                 return b
                                   Just b  -> do return b

