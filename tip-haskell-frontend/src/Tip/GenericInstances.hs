{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, ViewPatterns, ExplicitForAll #-}
{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, NamedFieldPuns #-}
-- | Data.Generic.Geniplate instances for GHC
module Tip.GenericInstances (module Tip.GenericInstances, module Data.Generics.Geniplate) where

import CoreSyn
import Data.Generics.Geniplate

import Var
import Coercion
import Id
import Literal
import Type
import DataCon

instanceTransformBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|AltCon|] ]
    [t| forall a . (Expr a,Expr a) |]

instanceTransformBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|AltCon|] ]
    [t| forall a . (Expr a,[Bind a]) |]

instanceTransformBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|AltCon|] ]
    [t| forall a . (Expr a,[(a,Expr a)]) |]

instanceUniverseBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|AltCon|] ]
    [t| forall a . (Expr a,Expr a) |]

instanceUniverseBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|DataCon|] ]
    [t| forall a . (Expr a,AltCon) |]
