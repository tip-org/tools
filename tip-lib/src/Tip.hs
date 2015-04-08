{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE ExplicitForAll, FlexibleContexts, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}
module Tip(module Tip, module Tip.Types) where

#include "errors.h"
import Tip.Types
import Tip.Fresh
import Tip.Utils
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Graph
import Data.Generics.Geniplate
import Data.List ((\\))
import Control.Monad
import qualified Data.Map as Map

updateLocalType :: Type a -> Local a -> Local a
updateLocalType ty (Local name _) = Local name ty

infix  4 ===
--infixr 3 /\
infixr 2 \/
infixr 1 ==>
infixr 0 ===>

(===) :: Expr a -> Expr a -> Expr a
e1 === e2 = Builtin Equal :@: [e1,e2]

neg :: Expr a -> Expr a
neg e = Builtin Not :@: [e]

(/\) :: Expr a -> Expr a -> Expr a
e1 /\ e2 = Builtin And :@: [e1,e2]

(\/) :: Expr a -> Expr a -> Expr a
e1 \/ e2 = Builtin Or :@: [e1,e2]

ands :: [Expr a] -> Expr a
ands [] = bool True
ands xs = foldl1 (/\) xs

(==>) :: Expr a -> Expr a -> Expr a
a ==> b = Builtin Implies :@: [a,b]

(===>) :: [Expr a] -> Expr a -> Expr a
xs ===> y = foldr (==>) y xs

mkQuant :: Quant -> [Local a] -> Expr a -> Expr a
mkQuant = Quant NoInfo

bool :: Bool -> Expr a
bool = literal . Bool

intLit :: Integer -> Expr a
intLit = literal . Int

literal :: Lit -> Expr a
literal lit = Builtin (Lit lit) :@: []

applyFunction :: Function a -> [Type a] -> [Expr a] -> Expr a
applyFunction fn@Function{..} tyargs args
  = Gbl (Global func_name (funcType fn) tyargs) :@: args

applyAbsFunc :: AbsFunc a -> [Type a] -> [Expr a] -> Expr a
applyAbsFunc AbsFunc{..} tyargs args
  = Gbl (Global abs_func_name abs_func_type tyargs) :@: args

atomic :: Expr a -> Bool
atomic (_ :@: []) = True
atomic Lcl{}      = True
atomic _          = False

absFunc :: Function a -> AbsFunc a
absFunc func@Function{..} = AbsFunc func_name (funcType func)

funcType :: Function a -> PolyType a
funcType (Function _ tvs lcls res _) = PolyType tvs (map lcl_type lcls) res

updateFuncType :: PolyType a -> Function a -> Function a
updateFuncType (PolyType tvs lclTys res) (Function name _ lcls _ body)
  | length lcls == length lclTys =
      Function name tvs (zipWith updateLocalType lclTys lcls) res body
  | otherwise = ERROR("non-matching type")

freshLocal :: Name a => Type a -> Fresh (Local a)
freshLocal ty = liftM2 Local fresh (return ty)

freshArgs :: Name a => Global a -> Fresh [Local a]
freshArgs gbl = mapM freshLocal (polytype_args (gbl_type gbl))

refreshLocal :: Name a => Local a -> Fresh (Local a)
refreshLocal (Local name ty) = liftM2 Local (refresh name) (return ty)

bound, free, locals :: Ord a => Expr a -> [Local a]
bound e =
  usort $
    concat [ lcls | Lam lcls _       <- universeBi e ] ++
           [ lcl  | Let lcl _ _      <- universeBi e ] ++
    concat [ lcls | Quant _ _ lcls _ <- universeBi e ] ++
    concat [ lcls | ConPat _ lcls    <- universeBi e ]
locals = usort . universeBi
free e = locals e \\ bound e

globals :: (UniverseBi (t a) (Global a),UniverseBi (t a) (Type a),Ord a)
        => t a -> [a]
globals e =
  usort $
    [ gbl_name | Global{..} <- universeBi e ] ++
    [ tc | TyCon tc _ <- universeBi e ]

tyVars :: Ord a => Type a -> [a]
tyVars t = usort $ [ a | TyVar a <- universeBi t ]

-- The free type variables are in the locals, and the globals:
-- but only in the types applied to the global variable.
freeTyVars :: Ord a => Expr a -> [a]
freeTyVars e =
  usort $
    concatMap tyVars $
             [ lcl_type | Local{..} <- universeBi e ] ++
      concat [ gbl_args | Global{..} <- universeBi e ]

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

matchTypesIn :: Ord a => [a] -> [(Type a, Type a)] -> Maybe [Type a]
matchTypesIn tvs tys = do
  sub <- matchTypes tys
  forM tvs $ \tv -> lookup tv sub

matchTypes :: Ord a => [(Type a, Type a)] -> Maybe [(a, Type a)]
matchTypes tys = mapM (uncurry match) tys >>= collect . usort . concat
  where
    match ty1 ty2 | ty1 == ty2 = Just []
    match (TyVar x) ty = Just [(x, ty)]
    match (TyCon x tys1) (TyCon y tys2)
      | x == y && length tys1 == length tys2 =
        fmap concat (zipWithM match tys1 tys2)
    match (args1 :=>: res1) (args2 :=>: res2)
      | length args1 == length args2 =
        fmap concat (zipWithM match (res1:args1) (res2:args2))
    match _ _ = Nothing

    collect [] = Just []
    collect [x] = Just [x]
    collect ((x, _):(y, _):_) | x == y = Nothing
    collect (x:xs) = fmap (x:) (collect xs)

apply :: Expr a -> [Expr a] -> Expr a
apply e es@(_:_) = Builtin At :@: (e:es)
apply _ [] = ERROR("tried to construct nullary lambda function")

applyType :: Ord a => [a] -> [Type a] -> Type a -> Type a
applyType tvs tys ty
  | length tvs == length tys =
      flip transformType ty $ \ty' ->
        case ty' of
          TyVar x ->
            Map.findWithDefault ty' x m
          _ -> ty'
  | otherwise = ERROR("wrong number of type arguments")
  where
    m = Map.fromList (zip tvs tys)

applyPolyType :: Ord a => PolyType a -> [Type a] -> ([Type a], Type a)
applyPolyType NoPolyType   tys = ([NoType | _ <- tys],NoType)
applyPolyType PolyType{..} tys =
  (map (applyType polytype_tvs tys) polytype_args,
   applyType polytype_tvs tys polytype_res)

exprType :: Ord a => Expr a -> Type a
exprType (Gbl (Global{..}) :@: _) = res
  where
    (_, res) = applyPolyType gbl_type gbl_args
exprType (Builtin blt :@: es) = builtinType blt (map exprType es)
exprType (Lcl lcl) = lcl_type lcl
exprType (Lam args body) = map lcl_type args :=>: exprType body
exprType (Match _ (Case _ body:_)) = exprType body
exprType (Match _ []) = ERROR("empty case expression")
exprType (Let _ _ body) = exprType body
exprType Quant{} = boolType

builtinType :: Ord a => Builtin -> [Type a] -> Type a
builtinType (Lit Int{}) _ = intType
builtinType (Lit Bool{}) _ = boolType
builtinType (Lit String{}) _ = ERROR("strings are not really here")
builtinType And _ = boolType
builtinType Or _ = boolType
builtinType Not _ = boolType
builtinType Implies _ = boolType
builtinType Equal _ = boolType
builtinType Distinct _ = boolType
builtinType IntAdd _ = intType
builtinType IntSub _ = intType
builtinType IntMul _ = intType
builtinType IntGt _ = boolType
builtinType IntGe _ = boolType
builtinType IntLt _ = boolType
builtinType IntLe _ = boolType
builtinType At ((_  :=>: res):_) = res
builtinType At _ = ERROR("ill-typed lambda application")

makeGlobal :: Ord a => a -> PolyType a -> [Type a] -> Maybe (Type a) -> Maybe (Global a)
makeGlobal name polyty@PolyType{..} args mres = do
  vars <- matchTypesIn polytype_tvs tys
  return (Global name polyty vars)
  where
    tys =
      (case mres of Nothing -> []; Just res -> [(polytype_res, res)]) ++
      zip polytype_args args

class Definition f where
  defines :: f a -> a
  uses    :: f a -> [a]

instance Definition Function where
  defines = func_name
  uses    = F.toList

instance Definition Datatype where
  defines = data_name
  uses    = F.toList

sortThings :: Ord name => (thing -> name) -> (thing -> [name]) -> [thing] -> [[thing]]
sortThings name refers things =
    map flattenSCC $ stronglyConnComp
        [ (thing,name thing,filter (`elem` names) (refers thing))
        | thing <- things
        ]
  where
    names = map name things

topsort :: (Ord a,Definition f) => [f a] -> [[f a]]
topsort = sortThings defines uses

ifView :: Expr a -> Maybe (Expr a,Expr a,Expr a)
ifView (Match c [Case _ e1,Case (LitPat (Bool b)) e2])
  | b         = Just (c,e2,e1)
  | otherwise = Just (c,e1,e2)
ifView (Match c [Case Default e1,Case (LitPat i@Int{}) e2])    = Just (c === literal i,e2,e1)
ifView (Match c (Case Default e1:Case (LitPat i@Int{}) e2:es)) = Just (c === literal i,e2,Match c (Case Default e1:es))
ifView _ = Nothing

makeIf :: Expr a -> Expr a -> Expr a -> Expr a
makeIf c t f = Match c [Case (LitPat (Bool True)) t,Case (LitPat (Bool False)) f]

-- Turn a Constructor into a Global.
constructorType :: Datatype a -> Constructor a -> PolyType a
constructorType Datatype{..} Constructor{..} =
  PolyType data_tvs (map snd con_args) (TyCon data_name (map TyVar data_tvs))

destructorType :: Datatype a -> Type a -> PolyType a
destructorType Datatype{..} ty =
  PolyType data_tvs [TyCon data_name (map TyVar data_tvs)] ty

constructor :: Datatype a -> Constructor a -> [Type a] -> Global a
constructor dt con@Constructor{..} tys =
  Global con_name (constructorType dt con) tys

projector :: Datatype a -> Constructor a -> Int -> [Type a] -> Global a
projector dt Constructor{..} i tys =
  Global proj_name (destructorType dt proj_ty) tys
  where
    (proj_name, proj_ty) = con_args !! i

discriminator :: Datatype a -> Constructor a -> [Type a] -> Global a
discriminator dt Constructor{..} tys =
  Global con_discrim (destructorType dt (BuiltinType Boolean)) tys

projAt :: Expr a -> Maybe (Expr a,Expr a)
projAt (Builtin At :@: [a,b]) = Just (a,b)
projAt _                          = Nothing

projGlobal :: Expr a -> Maybe a
projGlobal (Gbl (Global x _ _) :@: []) = Just x
projGlobal _                           = Nothing

intType :: Type a
intType = BuiltinType Integer

boolType :: Type a
boolType = BuiltinType Boolean

letExpr :: Name a => Expr a -> (Local a -> Fresh (Expr a)) -> Fresh (Expr a)
letExpr (Lcl x) k = k x
letExpr e k = freshLocal (exprType e) >>= k
