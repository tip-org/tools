{-# LANGUAGE FlexibleContexts, ViewPatterns, RecordWildCards #-}
module Tip.Pass.Booleans where

import Tip.Core

import Data.Generics.Geniplate

-- | Transforms boolean operators to if, but not in expression contexts.
theoryBoolOpToIf :: Ord a => Theory a -> Theory a
theoryBoolOpToIf Theory{..} =
  Theory{
    thy_funcs   = map boolOpToIf thy_funcs,
    thy_asserts =
      let k fm@Formula{..} = fm { fm_body = formulaBoolOpToIf fm_body }
      in  map k thy_asserts,
    ..
  }

formulaBoolOpToIf :: Ord a => Expr a -> Expr a
formulaBoolOpToIf e0 =
  case e0 of
    Builtin op :@: args@(a:_)
      | op `elem` [And,Or,Not,Implies] ||
        op `elem` [Equal,Distinct] && hasBoolType a ->
        Builtin op :@: map formulaBoolOpToIf args
    Quant qi q as e -> Quant qi q as (formulaBoolOpToIf e)
    _ -> boolOpToIf e0

hasBoolType :: Ord a => Expr a -> Bool
hasBoolType e = exprType e == boolType

-- | Transforms @and@, @or@, @=>@, @not@ and @=@ and @distinct@ on @Bool@
--   into @ite@ (i.e. @match@)
boolOpToIf :: (Ord a,TransformBi (Expr a) (f a)) => f a -> f a
boolOpToIf = transformExprIn $
  \ e0 -> case e0 of
    Builtin And :@: as  -> ands as
    Builtin Or  :@: as  -> ors  as
    Builtin Not :@: [a] -> neg_if a
    Builtin Implies :@: [a, b] -> makeIf a b trueExpr
    Builtin Equal :@: as | all hasBoolType as -> equals as
    Builtin Distinct :@: as | all hasBoolType as -> distincts as
    _ -> e0
  where
    ands []         = trueExpr
    ands [a]        = a
    ands (a:as)     = makeIf a (ands as) falseExpr
    ors  []         = falseExpr
    ors  [a]        = a
    ors  (a:as)     = makeIf a trueExpr (ors as)
    neg_if a        = makeIf a falseExpr trueExpr
    equals []       = trueExpr
    equals [_]      = trueExpr
    equals (a:as)   = makeIf a (ands as) (neg_if (ors as))
    distincts []    = trueExpr
    distincts [_]   = trueExpr
    distincts [a,b] = makeIf a (neg_if b) b
    distincts _     = falseExpr

-- | Transforms @ite@ (@match@) on boolean literals in the branches
--   into the corresponding builtin boolean function.
ifToBoolOp :: TransformBi (Expr a) (f a) => f a -> f a
ifToBoolOp = transformExprIn $
  \ e0 -> case ifView e0 of
    Just (b,t,f)
      | Just True  <- boolView t -> b \/ f
      | Just False <- boolView t -> neg b /\ f
      | Just True  <- boolView f -> b ==> t -- neg b \/ t
      | Just False <- boolView f -> b /\ t
    _ -> e0

