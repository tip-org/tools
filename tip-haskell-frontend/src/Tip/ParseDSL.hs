{-# LANGUAGE ViewPatterns #-}
-- | A hacky way of parsing the property language DSL
module Tip.ParseDSL where

import Tip.GHCUtils
import Tip.Id
import Tip.Core
import qualified Tip.CoreToTip as CTT

import qualified Data.Foldable as F

import Name hiding (varName)
import Data.List

import Var hiding (Id,isId)
import TyCon (TyCon)

nameInTip :: Name -> Bool
nameInTip = F.any (\ n -> showOutputable n == "Tip") . nameModule_maybe

varInTip :: Var -> Bool
varInTip = nameInTip . varName

idInTip :: Id -> Bool
idInTip = F.any nameInTip . tryGetGHCName

isId :: String -> Id -> Bool
isId s i = F.any (nameIs s) (tryGetGHCName i)

oneOf :: String -> String -> Id -> Bool
oneOf s1 s2 i = any (`isId` i) [s1,s2]

nameIs :: String -> Name -> Bool
nameIs s n = nameInTip n && s == showOutputable (nameOccName n)

varIs :: String -> Var -> Bool
varIs s v = nameIs s (varName v)

isPropType :: Type Id -> Bool
isPropType = goo 0 . res
  where
  go = goo 1
  goo i (BuiltinType Boolean) = i > 0
  goo i (TyCon tc [t1]) =  isId "Equality" tc || (isId "Neg" tc && go t1)
  goo i (TyCon tc [t1,t2]) =
    let ok xs = or [ isId s tc | s <- xs ]
    in     (ok ["And","Or",":=>:"] && go t1 && go t2)
        || (ok ["Forall","Exists"] && go t2)
  goo i _ = False

  res (_ :=>: r) = res r
  res r          = r

isPropTyCon :: Var -> Bool
isPropTyCon v =
    or [ varIs s v
       | s <- ["Equality","Neg","And","Or",":=>:","Forall","Exists"]
       ]

varWithPropType :: Var -> Bool
varWithPropType x = case CTT.trPolyType (varType x) of
    Right (PolyType _ _ t) -> isPropType t
    _                      -> False

