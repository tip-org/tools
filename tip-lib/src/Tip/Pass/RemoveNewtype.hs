{-# LANGUAGE RecordWildCards, PatternGuards, CPP #-}
module Tip.Pass.RemoveNewtype where

#include "errors.h"
import Tip.Core
import Tip.Fresh
import Tip.Scope
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Generics.Geniplate
import Data.Maybe

-- | Remove datatypes that have only one constructor with one field.
--   Can only be run after the @addMatch@ pass.
removeNewtype :: Name a => Theory a -> Theory a
removeNewtype thy@Theory{..} =
  -- Replace e.g.:
  -- I# x -> x
  -- (case x of _ -> e) -> e
  -- (case x of (I# y) -> e) -> let y = x in e
  -- Int -> Int#
  transformBi replaceTypes (replaceCons thy')
  where
    replaceTypes (TyCon ty []) =
      case lookupNewtype ty of
        Just ty' -> ty'
        Nothing -> TyCon ty []
    replaceTypes (args :=>: res) =
      map replaceTypes args :=>: replaceTypes res
    replaceTypes ty = ty

    replaceCons =
      transformBi $ \e0 ->
        case e0 of
          Match e cs | TyCon ty [] <- exprType e, isJust (lookupNewtype ty) ->
            case cs of
              Case Default body:_ -> body
              Case (ConPat _ [x]) body:_ -> Let x e body
              _ -> ERROR("type-incorrect pattern?")
          Gbl con :@: [e]
            | Just (dt, _) <- lookupConstructor (gbl_name con) scp
            , isJust (lookupNewtype (data_name dt)) ->
            e
          _ -> e0

    thy' =
      thy {
        thy_datatypes = [ d | d <- thy_datatypes, isNothing (lookupNewtype (data_name d)) ]}
    lookupNewtype ty = do
      Datatype{data_cons = [Constructor{con_args = [(_, ty')]}]} <- lookupDatatype ty scp
      return ty'
    scp = scope thy
