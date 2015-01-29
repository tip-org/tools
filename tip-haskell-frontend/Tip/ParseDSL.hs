{-# LANGUAGE ViewPatterns #-}
-- | A hacky way of parsing the property language DSL
module Tip.ParseDSL where

import Tip.GHCUtils
import Tip.Id
import Tip
import qualified Tip.CoreToTip as CTT

import Data.List

import Var hiding (Id)
import TyCon (TyCon)
--import Type
--import Outputable

-- import HipSpec.Id
-- import HipSpec.Lang.Type

varWithPropType :: Var -> Bool
varWithPropType x = case CTT.trPolyType (varType x) of
    Right (PolyType _ _ t) -> isPropType t
    _                      -> False

varFromPrelude :: Var -> Bool
varFromPrelude = isInfixOf "HipSpec" . showOutputable . varName

isPropTyCon :: TyCon -> Bool
isPropTyCon = isPropId . idFromTyCon

isPropType  :: Type Id -> Bool
isPropType t =
    case chaseResult t of
        TyCon p as -> isPropId p && not (any isPropType as)
        _          -> False

chaseResult (_ :=>: r) = chaseResult r
chaseResult r          = r

ghcName :: (String -> Bool) -> Id -> Bool
ghcName k (tryGetGHCName -> Just n) = k (showOutputable n)
ghcName _ _               = False

isPropId :: Id -> Bool
isPropId = ghcName (isInfixOf "HipSpec.Prop")
fromPrelude :: Id -> Bool
fromPrelude = ghcName (isInfixOf "HipSpec")

isMain      :: Id -> Bool
isMain      = ghcName (isInfixOf "main")

isEquals    :: Id -> Bool
isEquals    = ghcName (isInfixOfs [":=:","=:="])

isGiven     :: Id -> Bool
isGiven     = ghcName (isInfixOfs ["Given","given","==>"])

isTotal     :: Id -> Bool
isTotal     = ghcName (isInfixOfs ["Total","total"])

isGivenBool :: Id -> Bool
isGivenBool = ghcName (isInfixOf "givenBool")

isProveBool :: Id -> Bool
isProveBool = ghcName (isInfixOf "proveBool")

isOops      :: Id -> Bool
isOops      = ghcName (isInfixOfs ["Oops","oops"])

isInfixOfs :: [String] -> String -> Bool
isInfixOfs ss s = any (`isInfixOf` s) ss

