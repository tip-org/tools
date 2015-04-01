-- Remove datatypes that have only one constructor with one field.
-- Can only be run after the AddCase pass.
{-# LANGUAGE RecordWildCards, CPP #-}
module Tip.Denewtype where

#include "errors.h"
import Tip
import Tip.Fresh
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Generics.Geniplate

denewtype :: Name a => Theory a -> Theory a
denewtype thy@Theory{..} =
  -- Replace e.g.:
  -- I# x -> x
  -- (case x of _ -> e) -> e
  -- (case x of (I# y) -> e) -> let y = x in e
  -- Int -> Int#
  transformBi replaceTypes (replaceCons thy')
  where
    replaceTypes (TyCon ty []) =
      case Map.lookup ty tys of
        Nothing  -> TyCon ty []
        Just ty' -> ty'
    replaceTypes (args :=>: res) =
      map replaceTypes args :=>: replaceTypes res
    replaceTypes ty = ty

    replaceCons =
      transformBi $ \e0 ->
        case e0 of
          Match e cs | TyCon ty [] <- exprType e, ty `Map.member` tys ->
            case cs of
              Case Default body:_ -> body
              Case (ConPat _ [x]) body:_ -> Let x e body
              _ -> ERROR("type-incorrect pattern?")
          Gbl con :@: [e] | gbl_name con `Set.member` cons ->
            e
          _ -> e0
    
    thy' =
      thy {
        thy_data_decls = [ d | d <- thy_data_decls, not (Map.member (data_name d) tys) ] }
    singles = [(d, c, ty)
              | d@Datatype{data_cons = [c@Constructor{con_args=[(_, ty)]}],
                           data_tvs = []} <- thy_data_decls ]
    tys = Map.fromList [(data_name d, ty) | (d, _, ty) <- singles]
    cons = Set.fromList [con_name c | (_, c, _) <- singles]
