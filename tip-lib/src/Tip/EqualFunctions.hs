{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
module Tip.EqualFunctions(collapseEqual, removeAliases) where

import Tip
import Tip.Fresh

import Data.Traversable
import Control.Applicative
import Data.Either
import Data.List (delete, inits)

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad.State

renameVars :: forall f a . (Ord a,Traversable f) => (a -> Bool) -> f a -> f (Either a Int)
renameVars is_var t = runFresh (evalStateT (traverse rename t) M.empty)
  where
    rename :: a -> StateT (Map a Int) Fresh (Either a Int)
    rename x | is_var x = do my <- gets (M.lookup x)
                             case my of
                               Just y  -> do return (Right y)
                               Nothing -> do y <- lift fresh
                                             modify (M.insert x y)
                                             return (Right y)
    rename x = return (Left x)

renameFn :: Ord a => Function a -> Function (Either a Int)
renameFn fn = renameVars (`notElem` gbls) fn
  where
    gbls = delete (func_name fn) (globals fn)

rename :: Eq a => [(a,a)] -> a -> a
rename d x = case lookup x d of
    Just y  -> y
    Nothing -> x

-- If we have
--   f x = E[x]
--   g y = E[y]
-- then we remove g and replace it with f everywhere
collapseEqual :: forall a . Ord a => Theory a -> Theory a
collapseEqual thy@(Theory{ thy_func_decls = fns0 })
    = fmap (rename renamings) thy{ thy_func_decls = survivors }
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

-- | Pair up a list with its previous elements
--
-- > withPrevious "abc" = [('a',""),('b',"a"),('c',"ab")]
withPrevious :: [a] -> [(a,[a])]
withPrevious xs = zip xs (inits xs)

-- If we have
--    g x y = f x y
-- then we remove g and replace it with f everywhere
removeAliases :: Eq a => Theory a -> Theory a
removeAliases thy@(Theory{thy_func_decls=fns0})
    = fmap (rename renamings) thy{ thy_func_decls = survivors }
  where
    renamings =
      [ (g,f)
      | Function g ty_vars vars _res_ty (Gbl (Global f _ ty_args _) :@: args) <- fns0
      , map Lcl vars == args
      , map TyVar ty_vars == ty_args
      ]

    remove = map fst renamings

    survivors = filter ((`notElem` remove) . func_name) fns0

