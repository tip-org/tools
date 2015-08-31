{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns #-}
module Tip.Property where

import Tip.Core
import Tip.Id
import Tip.Pretty
import Tip.Pretty.SMT

import Tip.ParseDSL
import Tip.GHCUtils

import Control.Monad.Error
import Control.Applicative
import Data.Foldable (Foldable)
import Data.List (intercalate,union)
import Data.Map (Map)
import Data.Maybe (mapMaybe)
import Data.Traversable (Traversable)
import qualified Data.Map as M
-- import Text.PrettyPrint hiding (comma)

import Var (Var)
import TysWiredIn (trueDataCon,falseDataCon,boolTyCon)
-- import DataCon (dataConName)

-- | Translates a property that has been translated to a simple function earlier
trProperty :: Function Id -> Either String (Formula Id)
trProperty (Function _name tvs [] res_ty b) = case unLam b of
  (args,e) -> do
    pr <- parseProperty e
    return (Formula Prove tvs (mkQuant Forall args pr))
  where
    unLam (Lam xs e) = let (ys,e') = unLam e in (xs ++ ys,e')
    unLam e          = ([],e)

-- | Tries to "parse" a property in the simple expression format
parseProperty :: Expr Id -> Either String (Expr Id)
parseProperty = goo 0
  where
  go = goo 1
  goo i e0@(projAt -> Just (projGlobal -> Just x,Lam bs e))

      | isId "forAll" x || isId "Forall" x = mkQuant Forall bs <$> go e

      | isId "exists" x || isId "Exists" x = mkQuant Exists bs <$> go e

  goo i e0@(projAt -> Just (projGlobal -> Just x,e))

      | isId "bool" x = return e

      | isId "Neg" x || isId "neg" x || isId "question" x = neg <$> go e

  goo i e0@(projAt -> Just (projAt -> Just (projGlobal -> Just x,e1),e2))

      | isId "===" x || isId ":=:" x = return (e1 === e2)

      | isId "=/=" x                 = return (e1 =/= e2)

      | isId "==>" x || isId "Given" x = (==>) <$> go e1 <*> go e2

      | isId ".&&." x || isId "And" x  = (/\) <$> go e1 <*> go e2

      | isId ".||." x || isId "Or" x   = (\/) <$> go e1 <*> go e2

  goo i e0 | i > 0 && exprType e0 == boolType = return e0

  goo i e0 = throwError $ "Cannot parse property: " ++ ppRender e0

