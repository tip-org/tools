-- Fill in any missing match with a default value.

{-# LANGUAGE RecordWildCards #-}
module Tip.Pass.MakeMatchExhaustive where

import Tip.Core
import Tip.Scope
import Tip.Utils
import Tip.Fresh
import Data.Generics.Geniplate

makeMatchExhaustive :: Name a => Theory a -> Fresh (Theory a)
makeMatchExhaustive thy
  | and [ exhaustive (exprType val) (map case_pat cases) | Match val cases <- universeBi thy ] =
    return thy
  | otherwise = do
    undefinedName <- freshNamed "undefined"
    tv <- freshNamed "a"

    let
      undefinedSig =
        Signature undefinedName
          (putAttr (unitAttr "undefined") () [])
          undefinedType
      undefinedType = PolyType [tv] [] (TyVar tv)
      undefinedAt ty =
        Gbl (Global undefinedName undefinedType [ty]) :@: []
      addUndefined thy = thy{thy_sigs = undefinedSig:thy_sigs thy}

    return $
      addUndefined $
      flip transformExprIn thy $ \e ->
        case e of
          Match val cases
            | not (exhaustive (exprType val) (map case_pat cases)) ->
              Match val (Case Default (undefinedAt (exprType e)):cases)
          _ -> e
  where
    exhaustive _ (Default:_) = True
    exhaustive (TyCon ty _) pats =
      case lookupType ty scp of
        Just (DatatypeInfo Datatype{..}) ->
          usort (map con_name data_cons) ==
          usort [ gbl_name pat_con | ConPat{..} <- pats ]
        _ -> False
    exhaustive (BuiltinType Boolean) pats =
      usort pats == usort [LitPat (Bool False), LitPat (Bool True)]
    exhaustive _ _ = False

    scp = scope thy
