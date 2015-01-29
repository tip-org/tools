-- Generic support for the worker-wrapper transform.
{-# LANGUAGE PatternGuards, RecordWildCards #-}
module Tip.WorkerWrapper where

import Tip
import Tip.Fresh
import Tip.Simplify
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)

data WorkerWrapper a = WorkerWrapper
  { ww_func :: Function a
  , ww_args :: [Local a]
  , ww_res  :: Type a
  , ww_def  :: Expr a -> Expr a
  , ww_use  :: Head a -> [Expr a] -> Fresh (Expr a)
  }

workerWrapper :: Name a => [WorkerWrapper a] -> [Function a] -> Fresh [Function a]
workerWrapper wws funcs =
  mapM (transformExprInM updateUse . updateDef) funcs >>= mapM (simplifyExpr gently)
  where
    m = Map.fromList [(func_name (ww_func ww), ww) | ww <- wws]
    updateDef func@Function{..} =
      case Map.lookup func_name m of
        Nothing -> func
        Just WorkerWrapper{..} ->
          Function {
            func_args = ww_args, func_res = ww_res,
            func_body = ww_def func_body
          }
    updateUse e@(Gbl gbl@Global{..} :@: args)
      | Just WorkerWrapper{..} <- Map.lookup gbl_name m =
          let gbl_type' = gbl_type{polytype_args = map lcl_type ww_args,
                                   polytype_res = ww_res}
          in ww_use (Gbl gbl{gbl_type = gbl_type'}) args
      where
    updateUse e = return e
