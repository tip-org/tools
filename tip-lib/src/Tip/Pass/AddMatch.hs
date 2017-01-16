{-# LANGUAGE PatternGuards, RecordWildCards #-}
module Tip.Pass.AddMatch where

import Tip.Core
import Tip.Fresh
import Tip.Scope

-- | Replace SMTLIB-style selector and discriminator functions
--   (@is-nil@, @head@, @tail@) with case expressions.
addMatch :: Name a => Theory a -> Fresh (Theory a)
addMatch thy =
  flip transformExprInM thy $ \e ->
    case e of
      Gbl Global{..} :@: [t] | Just (d, c) <- lookupDiscriminator gbl_name scp -> do
        let con = constructor d c gbl_args
        args <- freshArgs con
        return $
          Match t [
            Case Default (bool False),
            Case (ConPat con args) (bool True) ]
      Gbl Global{..} :@: [t] | Just (d, c, i, _) <- lookupProjector gbl_name scp -> do
        let con = constructor d c gbl_args
        args <- freshArgs con
        return $
          Match t [
            Case (ConPat con args) (Lcl (args !! i)) ]
      _ -> return e
  where
    scp = scope thy
