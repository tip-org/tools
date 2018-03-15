-- | Evaluation of tip terms.

{-# LANGUAGE RecordWildCards #-}
module Tip.Eval where

import Tip.Core
import Tip.Scope
import Tip.Pretty
import Data.Map(Map)
import qualified Data.Map.Strict as Map
import Data.List
import Data.Maybe

-- | A value.
data Value a =
    IntVal Integer
  | RatVal Rational
  | BoolVal Bool
  | FuncVal (Type a) ([Value a] -> Value a)
  | ConVal (Type a) Int a [Value a]

valueType :: Value a -> Type a
valueType (IntVal _) = BuiltinType Integer
valueType (RatVal _) = BuiltinType Real
valueType (BoolVal _) = BuiltinType Boolean
valueType (FuncVal ty _) = ty
valueType (ConVal ty _ _ _) = ty

instance Eq a => Eq (Value a) where
  IntVal x == IntVal y = x == y
  RatVal x == RatVal y = x == y
  BoolVal x == BoolVal y = x == y
  FuncVal{} == FuncVal{} =
    error "eval: can't test functions for equality"
  ConVal _ _ x vs == ConVal _ _ y ws = x == y && vs == ws
  _ == _ = False

data Evaluator a =
  Evaluator {
    -- | Evaluate an uninterpreted function symbol.
    eval_uninterpreted :: Global a -> [Value a] -> Value a }

-- | Evaluate an expression in an environment.
eval :: (PrettyVar a, Ord a) => Evaluator a -> Theory a -> Map a (Value a) -> Expr a -> Value a
eval Evaluator{..} thy env e =
  exp env e
  where
    scp = scope thy
    funcs = Map.fromList [(func_name x, x) | x <- thy_funcs thy]

    arity n env es
      | length es == n = exps env es
      | otherwise = error "eval: wrong number of arguments"

    exps env es = map (exp env) es
    bind env xs vs e
      | length xs == length vs =
        exp (Map.union env (Map.fromList (zip (map lcl_name xs) vs))) e
      | otherwise = error "eval: mismatched length in binder list"
    
    exp env (Builtin blt :@: es) =
      builtin blt (exps env es)
    exp env (Gbl gbl@Global{..} :@: es) =
      case whichGlobal gbl_name scp of
        FunctionInfo{} ->
          case Map.lookup gbl_name funcs of
            Just Function{..} ->
              bind Map.empty func_args (exps env es) func_body
            Nothing ->
              eval_uninterpreted gbl (exps env es)
        ConstructorInfo Datatype{..} con@Constructor{..} ->
          ConVal (snd (gblType gbl)) (fromJust (elemIndex con data_cons)) con_name (exps env es)
        ProjectorInfo _ Constructor{..} n _ ->
          case arity 1 env es of
            [ConVal _ _ x vs] | con_name == x -> vs !! n
            _ -> error "eval: inappropriate use of projection function"
        DiscriminatorInfo _ Constructor{..} ->
          case arity 1 env es of
            [ConVal _ _ x _] | con_name == x -> BoolVal True
            _ -> BoolVal False
    exp env (Lcl Local{..}) =
      Map.findWithDefault (error "eval: unbound variable") lcl_name env
    exp env (Lam xs e) =
      FuncVal (map lcl_type xs :=>: exprType e) $ \vs ->
        bind env xs vs e
    exp env (Match e cases) =
      match env (exp env e) (reverse cases)
    exp env (Let Local{..} e1 e2) =
      let v1 = exp env e1 in
      exp (Map.insert lcl_name v1 env) e2
    exp _ LetRec{} = error "eval: letrec not supported"
    exp env (Quant _ q xs e) =
      error "eval: quantification not supported"

    builtin At (FuncVal _ f:vs) = f vs
    builtin (Lit (Int x)) [] = IntVal x
    builtin (Lit (Bool x)) [] = BoolVal x
    builtin And vs = BoolVal (and (map unBool vs))
    builtin Or vs = BoolVal (or (map unBool vs))
    builtin Not [BoolVal x] = BoolVal (not x)
    builtin Implies [BoolVal x, BoolVal y] = BoolVal (not x || y)
    builtin Equal vs = BoolVal (length (nub vs) == 1)
    builtin Distinct vs = BoolVal (length (nub vs) == length vs)
    builtin NumAdd vs = foldr1 op vs
      where
        op (IntVal x) (IntVal y) = IntVal (x+y)
        op (RatVal x) (RatVal y) = RatVal (x+y)
        op _ _ = error "eval: ill-typed arithmetic expression"
    builtin NumSub [IntVal x, IntVal y] = IntVal (x-y)
    builtin NumSub [RatVal x, RatVal y] = RatVal (x-y)
    builtin NumMul vs = foldr1 op vs
      where
        op (IntVal x) (IntVal y) = IntVal (x*y)
        op (RatVal x) (RatVal y) = RatVal (x*y)
        op _ _ = error "eval: ill-typed arithmetic expression"
    builtin NumDiv [IntVal x, IntVal y] = IntVal (x `div` y)
    builtin NumDiv [RatVal x, RatVal y] = RatVal (x/y)
    builtin IntDiv [IntVal x, IntVal y] = IntVal (x `div` y)
    builtin IntMod [IntVal x, IntVal y] = IntVal (x `mod` y)
    builtin NumGt [IntVal x, IntVal y] = BoolVal (x > y)
    builtin NumGt [RatVal x, RatVal y] = BoolVal (x > y)
    builtin NumGe [IntVal x, IntVal y] = BoolVal (x >= y)
    builtin NumGe [RatVal x, RatVal y] = BoolVal (x >= y)
    builtin NumLt [IntVal x, IntVal y] = BoolVal (x < y)
    builtin NumLt [RatVal x, RatVal y] = BoolVal (x < y)
    builtin NumLe [IntVal x, IntVal y] = BoolVal (x <= y)
    builtin NumLe [RatVal x, RatVal y] = BoolVal (x <= y)
    builtin NumWiden [IntVal x] = RatVal (fromIntegral x)
    builtin _ _ = error "eval: ill-typed builtin"

    unBool (BoolVal x) = x
    unBool _ = error "eval: expected boolean literal"

    match env v (Case pat e:cases) =
      case match1 v pat of
        Nothing -> match env v cases
        Just (xs, vs) ->
          bind env xs vs e
    match _ _ [] = error "eval: missing case"

    match1 _ Default =
      Just ([],[])
    match1 (IntVal x) (LitPat (Int y))
      | x == y = Just ([],[])
    match1 (BoolVal x) (LitPat (Bool y))
      | x == y = Just ([],[])
    match1 (ConVal _ _ c vs) (ConPat Global{..} xs)
      | gbl_name == c = Just (xs, vs)
    match1 _ _ = Nothing
