-- Replace "fat arrow" (=>) functions with normal functions
-- wherever possible.

{-# LANGUAGE RecordWildCards #-}
module Tip.Delambda where

import Tip
import Tip.Fresh
import Tip.WorkerWrapper
import Data.Maybe

delambda :: Name a => Theory a -> Fresh (Theory a)
delambda thy@Theory{..} = do
  ww <- sequence (catMaybes (map outerDelambdaWW thy_func_decls))
  case ww of
    [] -> do
      ww' <- sequence (catMaybes (map innerDelambdaWW thy_func_decls))
      workerWrapper ww' thy
    _ ->
      workerWrapper ww thy >>= delambda

-- Transform A -> B => C into A B -> C.
outerDelambdaWW :: Name a => Function a -> Maybe (Fresh (WorkerWrapper a))
outerDelambdaWW func@Function{func_res = args :=>: res, ..} = Just $ do
  lcls <- mapM freshLocal args
  return WorkerWrapper {
    ww_func = func,
    ww_args = func_args ++ lcls,
    ww_res  = res,
    ww_def  = \e -> apply e (map Lcl lcls),
    ww_use  =
      \hd orig_args -> do
        new_args <- mapM freshLocal args
        return (Lam new_args (hd :@: (orig_args ++ map Lcl new_args)))
  }
outerDelambdaWW _ = Nothing

-- Transform A => B => C into A B => C.
innerDelambdaWW :: Name a => Function a -> Maybe (Fresh (WorkerWrapper a))
innerDelambdaWW _func = Nothing
