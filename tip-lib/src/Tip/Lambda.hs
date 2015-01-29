{-# LANGUAGE ScopedTypeVariables, RecordWildCards #-}
module Tip.Lambda where

import Tip
import Tip.Fresh

import Control.Applicative
import Control.Monad
import Control.Monad.Writer

-- | Defunctionalization.
--
-- Transforms
--
--    f x = ... \ y -> e [ x ] ...
--
-- into
--
--    f x = ... g x ...
--    g x = \ y -> e [ x ]
--
-- where g is a fresh function.
--
-- After this pass, lambdas only exist at the top level of functions
--
-- TODO; Fix: do this on every expression, to remember assert/prove
--       What to do with type variables and "phantom" type variables?
defunFunc :: forall a . Name a => Function a -> Fresh [Function a]
defunFunc Function{..} =
  do (new_body,new_fns) <- runWriterT $ transformExprInM defun func_body
     return (Function{func_body = new_body,..}:new_fns)
 where
  defun :: Expr a -> WriterT [Function a] Fresh (Expr a)
  defun e@(Lam lam_args lam_body) =
    do g_name <- lift (refresh func_name)
       let g_args = free e
       let g_type = map lcl_type lam_args :=>: exprType lam_body
       let g = Function g_name func_tvs g_args g_type (Lam lam_args lam_body)
       tell [g]
       return (applyFunction g (map Lcl g_args))
  defun e = return e

defunFunctions :: Name a => [Function a] -> Fresh [Function a]
defunFunctions fns = concat <$> mapM defunFunc fns

defunctionalize :: Name a => Theory a -> Fresh (Theory a)
defunctionalize Theory{..} =
  do fn_decls <- defunFunctions thy_func_decls
     return Theory{thy_func_decls = fn_decls,..}

