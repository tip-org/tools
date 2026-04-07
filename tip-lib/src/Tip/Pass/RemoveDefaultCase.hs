{-# LANGUAGE RecordWildCards #-}
module Tip.Pass.RemoveDefaultCase where

import Tip.Core
import Tip.Fresh
import Tip.Scope
import Data.Maybe

removeDefaultCase :: Name a => Theory a -> Fresh (Theory a)
removeDefaultCase thy = do
  let scp = scope thy
  flip transformExprInM thy $ \e ->
    case e of
       Match e (Case Default def:cases)
         | TyCon ty args <- exprType e,
           Just dt@Datatype{..} <- lookupDatatype ty scp -> do
             pats <- sequence [constructorPat dt args con | con <- missingCases dt cases]
             return (caseExpr e (cases ++ [Case pat def | pat <- pats]))
       _ -> return e

missingCases :: Name a => Datatype a -> [Case a] -> [Constructor a]
missingCases Datatype{..} cases =
  filter (not . matched) data_cons
  where
    matched Constructor{..} =
      con_name `elem` [ gbl_name pat_con | ConPat{..} <- map case_pat cases ]

constructorPat :: Name a => Datatype a -> [Type a] -> Constructor a -> Fresh (Pattern a)
constructorPat dt args con = fmap (ConPat gbl) (freshArgs gbl)
  where
    gbl = constructor dt con args
