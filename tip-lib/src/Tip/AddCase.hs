-- Replace SMTLIB-style selector and discriminator functions
-- (is-nil, head, tail) with case expressions.

{-# LANGUAGE PatternGuards, RecordWildCards #-}
module Tip.AddCase where

import Tip
import Tip.Fresh
import qualified Data.Map as Map
import Data.Map(Map)

addCase :: Name a => Theory a -> Fresh (Theory a)
addCase thy =
  flip transformExprInM thy $ \e ->
    case e of
      Gbl Global{..} :@: [t] | Just (d, c) <- Map.lookup gbl_name discrims -> do
        let con = constructor d c gbl_args
        args <- freshArgs con
        return $
          Match t [
            Case Default (bool False),
            Case (ConPat con args) (bool True) ]
      Gbl Global{..} :@: [t] | Just (d, c, i) <- Map.lookup gbl_name sels -> do
        let con = constructor d c gbl_args
        args <- freshArgs con
        return $
          Match t [
            Case (ConPat con args) (Lcl (args !! i)) ]
      _ -> return e
  where
    discrims = Map.fromList [(con_discrim c, (d, c)) | d <- thy_data_decls thy, c <- data_cons d]
    sels = Map.fromList [(s, (d, c, i)) | d <- thy_data_decls thy, c <- data_cons d, (i, (s, _)) <- zip [0..] (con_args c)]
