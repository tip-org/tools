{-# LANGUAGE PatternGuards, RecordWildCards #-}
module Tip.Pass.CSEMatch where

import Tip.Core
import Tip.Fresh

data CSEMatchOpts =
  CSEMatchOpts {
    cse_nullary :: Bool
    -- ^ Also do CSE for nullary constructors
  }

cseMatchNormal, cseMatchWhy3 :: CSEMatchOpts
cseMatchNormal = CSEMatchOpts False
cseMatchWhy3   = CSEMatchOpts True

-- | Look for expressions of the form
--   @(match x (case P ...P...) ...)@
-- and replace them with
--   @(match x (case P ...x...) ...)@.
-- This helps Why3's termination checker in some cases.
cseMatch :: Name a => CSEMatchOpts -> Theory a -> Theory a
cseMatch CSEMatchOpts{..} =
  transformExprIn $ \e ->
    case e of
      Match (Lcl x) pats ->
        Match (Lcl x) (map (replaceWith x) pats)
      _ -> e
  where
    replaceWith x (Case (ConPat con args) body)
      | length args > 0 || cse_nullary =
        Case (ConPat con args) $
        flip transformExpr body $ \e ->
          if e == Gbl con :@: map Lcl args
          then Lcl x
          else e
    replaceWith x case_ = case_
