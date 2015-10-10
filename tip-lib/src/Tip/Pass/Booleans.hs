{-# LANGUAGE FlexibleContexts, ViewPatterns, RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.Booleans where

import Tip.Core

import Tip.Fresh

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

-- | Names to replace the builtin boolean type with
data BoolNames a =
  BoolNames
    { boolName    :: a
    , trueName    :: a
    , falseName   :: a
    , isTrueName  :: a
    , isFalseName :: a
    }

freshBoolNames :: Name a => Fresh (BoolNames a)
freshBoolNames =
  do boolName    <- freshNamed "Bool"
     trueName    <- freshNamed "True"
     falseName   <- freshNamed "False"
     isTrueName  <- freshNamed "is-True"
     isFalseName <- freshNamed "is-False"
     return BoolNames{..}

boolGbl :: BoolNames a -> Bool -> Global a
boolGbl BoolNames{..} b = Global
  (if b then trueName else falseName)
  (PolyType [] [] (TyCon boolName []))
  []

boolExpr :: BoolNames a -> Bool -> Expr a
boolExpr names b = Gbl (boolGbl names b) :@: []

removeBuiltinBoolFrom :: forall f a . (TransformBi (Type a) (f a),TransformBi (Pattern a) (f a),TransformBi (Head a) (f a)) => BoolNames a -> f a -> f a
removeBuiltinBoolFrom names = transformBi h . transformBi f . transformBi g
  where
    f :: Head a -> Head a
    f (Builtin (Lit (Bool b))) = Gbl (boolGbl names b)
    f hd                       = hd

    g :: Pattern a -> Pattern a
    g (LitPat (Bool b))    = ConPat (boolGbl names b) []
    g pat                  = pat

    h :: Type a -> Type a
    h (BuiltinType Boolean) = TyCon (boolName names) []
    h ty                    = ty

removeBuiltinBoolWith :: BoolNames a -> Theory a -> Theory a
removeBuiltinBoolWith names@BoolNames{..} Theory{..}
  = removeBuiltinBoolFrom names Theory{thy_datatypes=bool_decl:thy_datatypes,..}
  where
    bool_decl = Datatype boolName [] [Constructor falseName isFalseName []
                                     ,Constructor trueName isTrueName []]

removeBuiltinBool :: Name a => Theory a -> Fresh (Theory a)
removeBuiltinBool thy = do names <- freshBoolNames
                           return (removeBuiltinBoolWith names thy)

