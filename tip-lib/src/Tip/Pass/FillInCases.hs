-- Fill in any missing cases with a default value.

{-# LANGUAGE RecordWildCards #-}
module Tip.Pass.FillInCases where

import Tip.Core
import Tip.Scope
import Tip.Utils
import Tip.Pretty

fillInCases :: (Ord a, PrettyVar a) => (Type a -> Expr a) -> Theory a -> Theory a
fillInCases def thy =
  flip transformExprIn thy $ \e ->
    case e of
      Match val cases
        | not (exhaustive (exprType val) (map case_pat cases)) ->
          Match val (Case Default (def (exprType e)):cases)
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
