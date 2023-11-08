{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.IntroduceFuncdefs where

#include "errors.h"
import Tip.Core

import Control.Monad

-- | Convert functions which are defined using an axiom into define-fun.
-- e.g.:
-- (declare-fun f (Int Int) Int)
-- (assert (forall ((x Int) (y Int)) (= (f x y) ...)))
-- =>
-- (define-fun f (((x Int) (y Int)) Int) ...)
introduceFuncdefs :: Ord a => Theory a -> Theory a
introduceFuncdefs thy =
  foldr addAssert thy{thy_asserts = []} (thy_asserts thy)
  where
    addAssert fm thy =
      case extractDefinition fm of
        Just func | or [ sig_name sig == func_name func | sig <- thy_sigs thy ] ->
          thy {
            thy_funcs = func:thy_funcs thy,
            thy_sigs = [sig | sig <- thy_sigs thy, sig_name sig /= func_name func]}
        _ -> thy{thy_asserts = fm:thy_asserts thy}

-- Convert (if possible) a definition into a define-fun.
extractDefinition :: Ord a => Formula a -> Maybe (Function a)
extractDefinition fm =
  case fm of
    -- TODO: support polymorphic functions
    Formula Assert attrs [] (Builtin Equal :@: [Gbl gbl :@: [], def]) ->
      makeDef attrs gbl [] def
    Formula Assert attrs [] (Quant _ Forall _ (Builtin Equal :@: [Gbl gbl :@: args, def])) ->
      makeDef attrs gbl args def
    _ -> Nothing
  where
    makeDef attrs Global{..} args def = do
      guard (all isVar args)
      guard (null gbl_args)
      let vars = map unVar args
      return (Function gbl_name attrs [] vars (exprType def) def)

    isVar (Lcl _) = True
    isVar _ = False
    unVar (Lcl x) = x
    unVar _ = undefined
