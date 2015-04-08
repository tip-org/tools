-- Generic support for the worker-wrapper transform.
{-# LANGUAGE PatternGuards, RecordWildCards #-}
module Tip.WorkerWrapper where

import Tip
import Tip.Fresh
import Tip.Simplify
import qualified Data.Map as Map
import Data.Maybe

data WorkerWrapper a = WorkerWrapper
  { ww_func :: Function a                           -- ^ The function to transform
  , ww_args :: [Local a]                            -- ^ New function argument type
  , ww_res  :: Type a                               -- ^ New function result type
  , ww_def  :: Expr a -> Expr a                     -- ^ Transform function body
  , ww_use  :: Head a -> [Expr a] -> Fresh (Expr a) -- ^ Transform call to function
  }

workerWrapperTheory :: Name a => (Theory a -> Fresh [WorkerWrapper a]) -> Theory a -> Fresh (Theory a)
workerWrapperTheory f thy = do
  ww <- f thy
  case ww of
    [] -> return thy
    _ -> workerWrapper ww thy >>= workerWrapperTheory f

workerWrapperFunctions :: Name a => (Function a -> Maybe (Fresh (WorkerWrapper a))) -> Theory a -> Fresh (Theory a)
workerWrapperFunctions f =
  workerWrapperTheory (sequence . catMaybes . map f . thy_func_decls)

workerWrapper :: Name a => [WorkerWrapper a] -> Theory a -> Fresh (Theory a)
workerWrapper wws thy@Theory{..} = do
  transformExprInM updateUse thy' >>= simplifyExpr gently
  where
    thy' = thy { thy_func_decls = map updateDef thy_func_decls }
    m = Map.fromList [(func_name (ww_func ww), ww) | ww <- wws]
    updateDef func@Function{..} =
      case Map.lookup func_name m of
        Nothing -> func
        Just WorkerWrapper{..} ->
          func {
            func_args = ww_args, func_res = ww_res,
            func_body = ww_def func_body
          }
    updateUse (Gbl gbl :@: args)
      | Just WorkerWrapper{ww_func=Function{..}, ..} <- Map.lookup (gbl_name gbl) m =
          let gbl_type = PolyType { polytype_tvs = func_tvs,
                                    polytype_args = map lcl_type ww_args,
                                    polytype_res = ww_res}
          in ww_use (Gbl gbl{gbl_type = gbl_type}) args
    updateUse e = return e
