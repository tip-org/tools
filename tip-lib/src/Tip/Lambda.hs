{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
module Tip.Lambda (defunctionalize) where

import Tip
import Tip.Fresh

import Data.Generics.Geniplate
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

type DefunM a = WriterT [Function a] Fresh

defunTop :: Name a => Expr a -> DefunM a (Expr a)
defunTop e0 =
  case e0 of
    Lam lam_args lam_body ->
      do g_name <- lift fresh
         let g_args = free e0
         let g_tvs  = freeTyVars e0
         let g_type = map lcl_type lam_args :=>: exprType lam_body
         let g = Function g_name g_tvs g_args g_type (Lam lam_args lam_body)
         tell [g]
         return (applyFunction g (map TyVar g_tvs) (map Lcl g_args))
    _ -> return e0

defunAnywhere :: (Name a,TransformBiM (DefunM a) (Expr a) (t a)) =>
                 t a -> Fresh (t a,[Function a])
defunAnywhere = runWriterT . transformExprInM defunTop

defunctionalize :: Name a => Theory a -> Fresh (Theory a)
defunctionalize thy0 =
  do (Theory{..},new_func_decls) <- defunAnywhere thy0
     return Theory{thy_func_decls = new_func_decls ++ thy_func_decls,..}

