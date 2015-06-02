{-# LANGUAGE FlexibleContexts #-}
module Tip.Pass.Booleans where

import Tip.Core

import Data.Generics.Geniplate

-- | Transforms @and@, @or@, @=>@ and @not@ into if (i.e. case)
boolOpToIf :: TransformBi (Expr a) (f a) => f a -> f a
boolOpToIf = transformExprIn $
  \ e0 -> case e0 of
    Builtin And :@: [a,b]     -> makeIf a b falseExpr
    Builtin Or  :@: [a,b]     -> makeIf a trueExpr b
    Builtin Not :@: [a]       -> makeIf a falseExpr trueExpr
    Builtin Implies :@: [a,b] -> makeIf a b trueExpr
    _ -> e0

-- | Transforms match with boolean literals in the branches
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

