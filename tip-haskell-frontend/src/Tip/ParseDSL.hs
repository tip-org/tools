{-# LANGUAGE ViewPatterns #-}
-- | A hacky way of parsing the property language DSL
module Tip.ParseDSL where

import Tip.GHCUtils
import Tip.Id
import Tip.Core
import qualified Tip.CoreToTip as CTT

import Name hiding (varName)
import Data.List

import Var hiding (Id)
import TyCon (TyCon)

varWithPropType :: Var -> Bool
varWithPropType x = case CTT.trPolyType (varType x) of
    Right (PolyType _ _ t) -> isPropType (chaseResult t)
    _                      -> False

varFromPrelude :: Var -> Bool
varFromPrelude = isInfixOf "Tip.DSL" . showName . varName

showName :: Name -> String
showName n
  | Just m <- nameModule_maybe n = showOutputable m ++ "." ++ showOutputable (nameOccName n)
  | otherwise = showOutputable n

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
ghcName k (tryGetGHCName -> Just n) = k (showName n)
ghcName _ _                         = False

isPropId :: Id -> Bool
isPropId = ghcName (isInfixOf "Tip.DSL.Prop")
fromPrelude :: Id -> Bool
fromPrelude = ghcName (isInfixOf "Tip.DSL")

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

