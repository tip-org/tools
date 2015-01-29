-- Replace "fat arrow" (=>) functions with normal functions
-- wherever possible.

{-# LANGUAGE RecordWildCards #-}
module Tip.Delambda where

import Tip
import Tip.Fresh
import Tip.WorkerWrapper
import Data.Generics.Geniplate
import Data.Maybe

delambda :: Name a => [Function a] -> Fresh [Function a]
delambda funcs = do
  ww <- sequence (catMaybes (map outerDelambdaWW funcs))
  case ww of
    [] -> do
      ww' <- sequence (catMaybes (map innerDelambdaWW funcs))
      workerWrapper ww' funcs
    _ ->
      workerWrapper ww funcs >>= delambda

-- Transform A -> B => C into A B -> C.
outerDelambdaWW :: Name a => Function a -> Maybe (Fresh (WorkerWrapper a))
outerDelambdaWW func@Function{func_res = args :=>: res, ..} = Just $ do
  locals <- mapM freshLocal args
  return WorkerWrapper {
    ww_func = func,
    ww_args = func_args ++ locals,
    ww_res  = res,
    ww_def  = \e -> apply e (map Lcl locals),
    ww_use  =
      \hd orig_args -> do
        new_args <- mapM freshLocal args
        return (Lam new_args (hd :@: (orig_args ++ map Lcl new_args)))
  }
outerDelambdaWW _ = Nothing

-- Transform A => B => C into A B => C.
innerDelambdaWW :: Name a => Function a -> Maybe (Fresh (WorkerWrapper a))
innerDelambdaWW func = Nothing
