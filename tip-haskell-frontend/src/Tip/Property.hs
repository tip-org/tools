{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns #-}
module Tip.Property where

import Tip
import Tip.Id
import Tip.Pretty

import Tip.ParseDSL
import Tip.GHCUtils

import Control.Monad.Error
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
    (assums,goal) <- parseProperty e
    return (Formula Prove tvs (mkQuant Forall args (assums ===> goal)))
  where
    unLam (Lam xs e) = let (ys,e') = unLam e in (xs ++ ys,e')
    unLam e          = ([],e)

-- | Tries to "parse" a property in the simple expression format
parseProperty :: Expr Id -> Either String ([Expr Id],Expr Id)
parseProperty e0@(projAt -> Just (projAt -> Just (projGlobal -> Just x,e1),e2))
  | isEquals x    = return ([],e1 === e2)
  | isGivenBool x = do (as,gl) <- parseProperty e2
                       return (e1:as,gl) -- e1 === tt?
  | isGiven x     = do (nested_as,a) <- parseProperty e1
                       unless (null nested_as) (throwError $ "Property with nested assumptions" ++ ppRender e0)
                       (as,gl) <- parseProperty e2
                       return (a:as,gl)
parseProperty (projAt -> Just (projGlobal -> Just x,e1))
  | isProveBool x = return ([],e1) -- e1 === tt?
parseProperty e0 = throwError $ "Cannot parse property: " ++ ppRender e0

projAt :: Expr a -> Maybe (Expr a,Expr a)
projAt (Builtin (At 1) :@: [a,b]) = Just (a,b)
projAt _                          = Nothing

projGlobal :: Expr a -> Maybe a
projGlobal (Gbl (Global x _ _ _) :@: []) = Just x
projGlobal _                             = Nothing

