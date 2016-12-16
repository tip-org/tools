{-# LANGUAGE RecordWildCards, CPP #-}
module Tip.Pass.RemoveMatch where

#include "errors.h"
import Tip.Core
import Tip.Fresh
import Tip.Scope
import Data.Generics.Geniplate

-- | Turn case expressions into @is-Cons@, @head@, @tail@ etc.
removeMatch :: Name a => Theory a -> Fresh (Theory a)
removeMatch thy@Theory{..} = transformBiM go thy
  where
    scp = scope thy
    go = transformBiM $ \e0 ->
      case e0 of
        Match e cs | all acceptable (map case_pat cs) ->
          letExpr e $ \x ->
            match x (reverse cs) >>= go
        _ -> return e0

    acceptable Default = True
    acceptable ConPat{} = True
    acceptable _ = False

    match x [Case (ConPat c xs) body] = caseBody x (gbl_name c) xs body
    match x [Case Default body] = return body
    match x (Case (ConPat c xs) body:cs) = do
      clause <- caseBody x (gbl_name c) xs body
      rest <- match x cs
      return $
        Match (matches x (gbl_name c))
          [Case Default rest,
           Case (LitPat (Bool True)) clause]
    match _ [] = ERROR("empty list of cases")
    match _ (Case Default _:_) = ERROR("default case not first in list of cases")
    match _ (Case LitPat{} _:_) = __

    matches x c =
      Gbl (uncurry discriminator (whichConstructor c scp) args) :@: [Lcl x]
      where
        TyCon _ args = lcl_type x

    caseBody x c lcls body = substMany sub body
      where
        sub = [(lcl, Gbl (uncurry projector (whichConstructor c scp) i args) :@: [Lcl x]) | (i, lcl) <- zip [0..] lcls]
        TyCon _ args = lcl_type x
