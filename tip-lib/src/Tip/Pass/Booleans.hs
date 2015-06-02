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

-- | Transforms @and@, @or@, @=>@, @not@ and @=@ and @distict@ on @Bool@
--   into @ite@ (i.e. @match@)
boolOpToIf :: (Ord a,TransformBi (Expr a) (f a)) => f a -> f a
boolOpToIf = transformExprIn $
  \ e0 -> case e0 of
    Builtin And :@: [a,b]     -> makeIf a b falseExpr
    Builtin Or  :@: [a,b]     -> makeIf a trueExpr b
    Builtin Not :@: [a]       -> makeIf a falseExpr trueExpr
    Builtin Implies :@: [a,b] -> makeIf a b trueExpr
    Builtin Equal    :@: [a,b] | hasBoolType a -> makeIf a b (neg_if b)
    Builtin Distinct :@: [a,b] | hasBoolType a -> makeIf a (neg_if b) b
    _ -> e0
  where
    neg_if a = makeIf a falseExpr trueExpr

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

