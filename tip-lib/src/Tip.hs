{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE ExplicitForAll, FlexibleContexts, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}
module Tip(module Tip, module Tip.Types) where

#include "errors.h"
import Tip.Types
import Tip.Fresh
import Tip.Utils
import Data.Generics.Geniplate
import Data.List ((\\))
import Control.Monad
import qualified Data.Map.Strict as Map

updateLocalType :: Type a -> Local a -> Local a
updateLocalType ty (Local name _) = Local name ty

(===) :: Expr a -> Expr a -> Expr a
e1 === e2 = Builtin Equal :@: [e1,e2]

(===>) :: [Expr a] -> Expr a -> Expr a
xs ===> y = foldr (\ a b -> Builtin Implies :@: [a,b]) y xs

mkQuant :: Quant -> [Local a] -> Expr a -> Expr a
mkQuant q xs t = foldr (Quant q) t xs

literal :: Lit -> Expr a
literal lit = Builtin (Lit lit) :@: []

global :: Global a -> Expr a
global gbl = Gbl gbl :@: []

atomic :: Expr a -> Bool
atomic (_ :@: []) = True
atomic Lcl{}      = True
atomic _          = False

funcType :: Function a -> PolyType a
funcType (Function _ tvs lcls res _) = PolyType tvs (map lcl_type lcls) res

updateFuncType :: PolyType a -> Function a -> Function a
updateFuncType (PolyType tvs lclTys res) (Function name _ lcls _ body)
  | length lcls == length lclTys =
      Function name tvs (zipWith updateLocalType lclTys lcls) res body
  | otherwise = ERROR("non-matching type")

freshLocal :: Name a => Type a -> Fresh (Local a)
freshLocal ty = liftM2 Local fresh (return ty)

refreshLocal :: Name a => Local a -> Fresh (Local a)
refreshLocal (Local name ty) = liftM2 Local (refresh name) (return ty)

bound, free, locals :: Ord a => Expr a -> [Local a]
bound e =
  usort $
    concat [ lcls | Lam lcls _    <- universeBi e ] ++
           [ lcl  | Let lcl _ _   <- universeBi e ] ++
           [ lcl  | Quant _ lcl _ <- universeBi e ] ++
    concat [ lcls | ConPat _ lcls <- universeBi e ]
locals = usort . universeBi
free e = locals e \\ bound e

-- Rename bound variables in an expression to fresh variables.
freshen :: Name a => Expr a -> Fresh (Expr a)
freshen e = do
  let lcls = bound e
  sub <- fmap (Map.fromList . zip lcls) (mapM refreshLocal lcls)
  return . flip transformBi e $ \lcl ->
    case Map.lookup lcl sub of
      Nothing -> lcl
      Just lcl' -> lcl'

-- | Substitution, of local variables
--
-- Since there are only rank-1 types, bound variables from lambdas and
-- case never have a forall type and thus are not applied to any types.
(//) :: Name a => Expr a -> Local a -> Expr a -> Fresh (Expr a)
e // x = transformExprM $ \ e0 -> case e0 of
  Lcl y | x == y -> freshen e
  _              -> return e0

substMany :: Name a => [(Local a, Expr a)] -> Expr a -> Fresh (Expr a)
substMany xs e0 = foldM (\e (x,xe) -> (xe // x) e) e0 xs

apply :: Expr a -> [Expr a] -> Expr a
apply e es@(_:_) = Builtin (At (length es)) :@: (e:es)
apply _ [] = ERROR("tried to construct nullary lambda function")

applyType :: Ord a => [a] -> [Type a] -> Type a -> Type a
applyType tvs tys ty
  | length tvs == length tys =
      flip transformType ty $ \ty' ->
        case ty' of
          TyVar x ->
            Map.findWithDefault ty' x m
          _ -> ty
  | otherwise = ERROR("wrong number of type arguments")
  where
    m = Map.fromList (zip tvs tys)

applyPolyType :: Ord a => PolyType a -> [Type a] -> ([Type a], Type a)
applyPolyType PolyType{..} tys =
  (map (applyType polytype_tvs tys) polytype_args,
   applyType polytype_tvs tys polytype_res)

exprType :: Ord a => Expr a -> Type a
exprType (Gbl (Global{..}) :@: _) = res
  where
    (_, res) = applyPolyType gbl_type gbl_args
exprType (Builtin blt :@: es) = builtinType blt es
exprType (Lcl lcl) = lcl_type lcl
exprType (Lam args body) = map lcl_type args :=>: exprType body
exprType (Match _ (Case _ body:_)) = exprType body
exprType (Match _ []) = ERROR("empty case expression")
exprType (Let _ _ body) = exprType body
exprType Quant{} = BuiltinType Boolean

builtinType :: Ord a => Builtin -> [Expr a] -> Type a
builtinType (Lit Int{}) _ = BuiltinType Integer
builtinType (Lit Bool{}) _ = BuiltinType Boolean
builtinType (Lit String{}) _ = ERROR("strings are not really here")
builtinType And _ = BuiltinType Boolean
builtinType Or _ = BuiltinType Boolean
builtinType Implies _ = BuiltinType Boolean
builtinType Equal _ = BuiltinType Boolean
builtinType Distinct _ = BuiltinType Boolean
builtinType At{} (e:_) =
  case exprType e of
    _ :=>: res -> res
    _ -> ERROR("ill-typed lambda application")
builtinType At{} _ = ERROR("ill-formed lambda application")
