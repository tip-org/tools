{-# LANGUAGE CPP, RecordWildCards, OverloadedStrings, FlexibleContexts, ViewPatterns #-}
-- | Check that a theory is well-typed.
--
-- Invariants:
--
--  * No shadowing---checked by scope monad.
--
--  * Each local is bound before it's used.
--
--  * All expressions are well-typed.
--
--  * The result of each constructor should be a value of that datatype.
--
--  * Default case comes first. No duplicate cases.
--
--  * Expressions and formulas not mixed.
module Tip.Lint (lint, lintM, lintTheory) where

#include "errors.h"
import Tip
import Tip.Scope
import Tip.Pretty
import Tip.Renamer
import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import Data.Maybe
import Text.PrettyPrint
import Tip.Pretty.SMT
import Data.List
--import Debug.Trace

-- | Crashes if the theory is malformed
lint :: (PrettyVar a, Ord a) => String -> Theory a -> Theory a
lint pass thy0@(renameAvoiding [] return -> thy) =
  -- trace ("Linting:" ++ pass ++ ":\n" ++ ppRender thy) $
  case (lintTheory thy,lintTheory thy0) of
    (Just doc,_) -> error ("Lint failed after " ++ pass ++ ":\n" ++ show doc ++ "\n!!!")
    (_,Just doc) -> error ("Non-renamed linting pass failed!? " ++ pass ++ ":\n" ++ show doc ++ "\n!!!")
    (_,_)        -> thy0

-- | Same as 'lint', but returns in a monad, for convenience
lintM :: (PrettyVar a, Ord a, Monad m) => String -> Theory a -> m (Theory a)
lintM pass = return . lint pass

check :: (PrettyVar a, Ord a) => Doc -> (Scope a -> Bool) -> ScopeM a ()
check x p = check' x (guard . p)

check' :: (PrettyVar a, Ord a) => Doc -> (Scope a -> Maybe b) -> ScopeM a b
check' x p = do
  scp <- get
  case p scp of
    Nothing -> throwError x
    Just y  -> return y

-- | Returns the error if the theory is malformed
lintTheory :: (PrettyVar a, Ord a) => Theory a -> Maybe Doc
lintTheory thy@Theory{..} =
  either Just (const Nothing) .
  runScope . withTheory thy $ inContext thy $ do
    mapM_ lintDatatype thy_data_decls
    mapM_ lintAbsFunc thy_abs_func_decls
    mapM_ lintFunction thy_func_decls
    mapM_ lintFormula thy_form_decls

lintDatatype :: (PrettyVar a, Ord a) => Datatype a -> ScopeM a ()
lintDatatype dt@Datatype{..} =
  local $ inContext dt $ do
    mapM_ newTyVar data_tvs
    forM_ data_cons $ \Constructor{..} -> do
      forM_ con_args $ \(_, ty) ->
        lintType ty

lintPolyType :: (PrettyVar a, Ord a) => PolyType a -> ScopeM a ()
lintPolyType polyty@PolyType{..} =
  newScope $ inContext polyty $ do
    mapM_ newTyVar polytype_tvs
    mapM_ lintType polytype_args
    lintType polytype_res

lintType :: (PrettyVar a, Ord a) => Type a -> ScopeM a ()
lintType (TyVar x) =
  check (fsep ["Type variable", nest 2 (ppVar x), "not in scope"])
    (isTyVar x)
lintType (TyCon x tys) = do
  info <- check' (fsep ["Type constructor", nest 2 (ppVar x), "not in scope"])
    (lookupType x)
  let checkArity n =
        unless (n == length tys) $
          throwError $ fsep [
            "Type constructor", nest 2 (ppVar x),
            "of arity" <+> int n,
            "applied to" <+> int (length tys) <+> "type arguments"]
  case info of
    TyVarInfo ->
      throwError (fsep ["Type variable", nest 2 (ppVar x), "used as type constructor"])
    AbsTypeInfo n -> checkArity n
    DatatypeInfo Datatype{..} -> checkArity (length data_tvs)
  mapM_ lintType tys
lintType (args :=>: res) = do
  mapM_ lintType args
  lintType res
lintType BuiltinType{} = return ()
lintType NoType = return ()

lintAbsFunc :: (PrettyVar a, Ord a) => AbsFunc a -> ScopeM a ()
lintAbsFunc func@AbsFunc{..} =
  inContext func (lintPolyType abs_func_type)

lintFunction :: (PrettyVar a, Ord a) => Function a -> ScopeM a ()
lintFunction func@Function{..} =
  local $ inContext func $ do
    mapM_ newTyVar func_tvs
    mapM_ lintBinder func_args
    lintType func_res
    lintExpr ExprKind func_body
    unless (func_res == exprType func_body) $
      throwError (fsep [
        "Declared return type", nest 2 (pp func_res),
        "does not match actual return type", nest 2 (pp (exprType func_body))])

lintBinder :: (PrettyVar a, Ord a) => Local a -> ScopeM a ()
lintBinder lcl@Local{..} = do
  lintType lcl_type
  newLocal lcl

lintFormula :: (PrettyVar a, Ord a) => Formula a -> ScopeM a ()
lintFormula form@(Formula _ tvs expr) =
  local $ inContext form $ do
    mapM_ newTyVar tvs
    lintExpr FormulaKind expr
    unless (exprType expr == boolType) $
      throwError $
        fsep ["Formula has non-boolean type", nest 2 (pp (exprType expr))]

data ExprKind = ExprKind | FormulaKind deriving Eq

lintExpr :: (PrettyVar a, Ord a) => ExprKind -> Expr a -> ScopeM a ()
lintExpr _ (Gbl gbl@Global{..} :@: exprs) = do
  lintGlobal gbl
  mapM_ (lintExpr ExprKind) exprs
  let (args, _) = applyPolyType gbl_type gbl_args
  lintCall (Gbl gbl) exprs args
lintExpr kind (Builtin bltin :@: exprs) = do
  mapM_ (lintExpr (if isExpression bltin then ExprKind else kind)) exprs
  tys <- lintBuiltin bltin (map exprType exprs)
  lintCall (Builtin bltin) exprs tys
lintExpr _ (Lcl lcl@Local{..}) = do
  check ("Unbound variable" <+> pp lcl) (isLocal lcl_name)
  check ("Inconsistent type for local" <+> pp lcl) $
    \scp -> whichLocal lcl_name scp == lcl_type
lintExpr kind (Lam lcls expr) =
  local $ do
    mapM_ lintBinder lcls
    lintExpr ExprKind expr
lintExpr kind (Match expr cases) = do
  lintExpr (if kind == FormulaKind && exprType expr /= boolType then ExprKind else kind)
    expr
  when (null cases) $
    throwError "Case with no alternatives"
  mapM_ (lintCase kind expr) cases

  when (Default `elem` drop 1 (map case_pat cases)) $
    throwError "Default case is in wrong position"
  unless (Default `elem` map case_pat cases) $ do
    let strip (ConPat gbl _) = ConPat gbl []
        strip x = x
        stripped = map (strip . case_pat) cases
    unless (nub stripped == stripped) $
      throwError "The same constructor appears several times"
  unless (length (nub (map (exprType . case_rhs) cases)) == 1) $
    throwError "Not all case clauses have the same type"
lintExpr kind (Let lcl@Local{..} expr body) = do
  lintExpr ExprKind expr
  local $ do
    lintBinder lcl
    lintExpr kind body
  unless (lcl_type == exprType expr) $
    throwError (fsep [
      "Expression of type", nest 2 (pp (exprType expr)),
      "bound to variable" <+> pp lcl,
      "of type", nest 2 (pp lcl_type)])
lintExpr ExprKind (Quant NoInfo _ lcls expr) =
  throwError "Quantifier found in expression"
lintExpr FormulaKind (Quant NoInfo _ lcls expr) =
  local $ do
    mapM_ lintBinder lcls
    lintExpr FormulaKind expr

lintGlobal :: (PrettyVar a, Ord a) => Global a -> ScopeM a ()
lintGlobal gbl@Global{..} = do
  lintPolyType gbl_type
  mapM_ lintType gbl_args
  unless (length gbl_args == length (polytype_tvs gbl_type)) $
    throwError (fsep ["Global" <+> pp gbl, "applied to type arguments", nest 2 (vcat (map pp gbl_args)), "but expects" <+> int (length (polytype_tvs gbl_type))])
  check ("Unbound global" <+> pp gbl) (isGlobal gbl_name)
  -- scp <- get
  -- check (fsep ["Global" <> pp gbl, "is used with type", nest 2 (ppPolyType gbl_type), "but was declared with type", nest 2 (ppPolyType (globalType (whichGlobal gbl_name scp)))]) $
  --   \scp -> globalType (whichGlobal gbl_name scp) == gbl_type

lintCall :: (PrettyVar a, Ord a) => Head a -> [Expr a] -> [Type a] -> ScopeM a ()
lintCall hd exprs args =
  unless (args == map exprType exprs) $
    throwError (fsep ["Function" <+> pp hd, "which expects arguments of type", nest 2 (vcat (map pp args)), "applied to arguments of type", nest 2 (vcat (map pp (map exprType exprs))), "in", nest 2 (pp (hd :@: exprs))])

lintBuiltin :: (PrettyVar a, Ord a) => Builtin -> [Type a] -> ScopeM a [Type a]
lintBuiltin At [] = throwError "@ cannot have arity 0"
lintBuiltin At ((args :=>: res):_) =
  return ((args :=>: res):args)
lintBuiltin At (ty:_) =
  throwError (fsep ["First argument of @ has non-function type", nest 2 (pp ty)])
lintBuiltin Lit{} _ = return []
lintBuiltin And tys = return (replicate (length tys) boolType)
lintBuiltin Or tys = return (replicate (length tys) boolType)
lintBuiltin Not _ = return [boolType]
lintBuiltin Implies _ = return [boolType, boolType]
lintBuiltin Equal [] = throwError "Nullary ="
lintBuiltin Equal tys@(ty:_) = return (replicate (length tys) ty)
lintBuiltin Equal [] = throwError "Nullary distinct"
lintBuiltin Distinct tys@(ty:_) = return (replicate (length tys) ty)
lintBuiltin IntAdd tys = return (replicate (length tys) intType)
lintBuiltin IntSub _ = return [intType, intType]
lintBuiltin IntMul _ = return [intType, intType]
lintBuiltin IntDiv _ = return [intType, intType]
lintBuiltin IntMod _ = return [intType, intType]
lintBuiltin IntGt _ = return [intType, intType]
lintBuiltin IntGe _ = return [intType, intType]
lintBuiltin IntLt _ = return [intType, intType]
lintBuiltin IntLe _ = return [intType, intType]

isExpression :: Builtin -> Bool
isExpression Equal = True
isExpression Distinct = True
isExpression IntGt = True
isExpression IntGe = True
isExpression IntLt = True
isExpression IntLe = True
isExpression _ = False

lintCase :: (PrettyVar a, Ord a) => ExprKind -> Expr a -> Case a -> ScopeM a ()
lintCase kind _ (Case Default body) = lintExpr kind body
lintCase kind _ (Case LitPat{} body) = lintExpr kind body
lintCase kind expr (Case (ConPat gbl@Global{..} args) body) =
  local $ do
    mapM_ lintBinder args
    lintExpr kind (Gbl gbl :@: map Lcl args)
    lintExpr kind body
    check ("Global" <+> pp gbl <+> "used as constructor")
      (isJust . lookupConstructor gbl_name)
    let (_, res) = applyPolyType gbl_type gbl_args
    unless (res == exprType expr) $
      throwError (fsep ["Constructor", nest 2 (pp (Gbl gbl :@: map Lcl args)), "has type", nest 2 (pp res), "but should be", nest 2 (pp (exprType expr))])
