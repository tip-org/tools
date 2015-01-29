{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE ExplicitForAll, FlexibleContexts, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
module Tip where

import Tip.Fresh
import Data.Generics.Geniplate
import Data.List (nub)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Control.Monad

data Head a
  = Gbl (Global a)
  | Builtin Builtin
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Local a = Local { lcl_name :: a, lcl_type :: Type a }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

updateLocalType :: Type a -> Local a -> Local a
updateLocalType ty (Local name _) = Local name ty

data Global a = Global
  { gbl_name      :: a
  , gbl_type      :: PolyType a
  , gbl_args      :: [Type a]
  , gbl_namespace :: Namespace
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Namespace = FunctionNS | ConstructorNS
  deriving (Eq,Ord,Show)

data Expr a
  = Head a :@: [Expr a]
  | Lcl (Local a)
  | Lam [Local a] (Expr a)
  | Case (Expr a) [Alt a]
  | Let (Local a) (Expr a) (Expr a)
  | Quant Quant (Local a) (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Quant = Forall | Exists
  deriving (Eq,Ord,Show)

literal :: Lit -> Expr a
literal lit = Builtin (Lit lit) :@: []

global :: Global a -> Expr a
global gbl = Gbl gbl :@: []

type Alt a = (Pattern a,Expr a)

data Builtin
  = Lit Lit
  | And | Or | Implies
  | Equal | Distinct
  | At Int
  deriving (Eq,Ord,Show)

(===) :: Expr a -> Expr a -> Expr a
e1 === e2 = Builtin Equal :@: [e1,e2]

(===>) :: [Expr a] -> Expr a -> Expr a
xs ===> y = foldr (\ a b -> Builtin Implies :@: [a,b]) y xs

mkQuant :: Quant -> [Local a] -> Expr a -> Expr a
mkQuant q xs t = foldr (Quant q) t xs

data Lit
  = Int Integer
  | Bool Bool
  | String String -- Not really here but might come from GHC
  deriving (Eq,Ord,Show)

-- | Patterns in branches
data Pattern a
  = Default
  | ConPat { pat_con  :: Global a, pat_args :: [Local a] }
  | LitPat Lit
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Polymorphic types
data PolyType a = PolyType
  { polytype_tvs  :: [a]
  , polytype_args :: [Type a]
  , polytype_res  :: Type a
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Types
data Type a
  = TyVar a
  | TyCon a [Type a]
  | [Type a] :=>: Type a
  | Integer
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Function a = Function
  { func_name :: a
  , func_tvs  :: [a]
  , func_args :: [Local a]
  , func_res  :: Type a
  , func_body :: Expr a
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

funcType :: Function a -> PolyType a
funcType (Function _ tvs lcls res _) = PolyType tvs (map lcl_type lcls) res

updateFuncType :: PolyType a -> Function a -> Function a
updateFuncType (PolyType tvs lclTys res) (Function name _ lcls _ body)
  | length lcls == length lclTys =
      Function name tvs (zipWith updateLocalType lclTys lcls) res body

-- | Data definition
data Datatype a = Datatype
  { data_ty_con :: a
  , data_tvs    :: [a]
  , data_cons   :: [Constructor a]
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Constructor a = Constructor
  { con_name :: a
  , con_args :: [Type a]
  -- ^ Arguments to the constructor, /besides/ the type
  --   arguments that are bound in the data type
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Decl a
  = FunDecl (Function a)
  | DataDecl (Datatype a)
  | FormDecl (Formula a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Formula a = Formula Role [a] {- ^ type variables -} (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Role = Assert | Prove
  deriving (Eq,Ord,Show)

instanceTransformBi [t| forall a . (Expr a,Expr a) |]
instanceTransformBi [t| forall a . (Expr a,Function a) |]
instance Monad m => TransformBiM m (Expr a) (Expr a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Expr a) (Function a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Function a -> m (Function a) |])

transformExpr :: (Expr a -> Expr a) -> Expr a -> Expr a
transformExpr = transformBi

transformExprM :: Monad m => (Expr a -> m (Expr a)) -> Expr a -> m (Expr a)
transformExprM = transformBiM

transformExprIn :: TransformBi (Expr a) (f a) => (Expr a -> Expr a) -> f a -> f a
transformExprIn = transformBi

transformExprInM :: TransformBiM m (Expr a) (f a) => (Expr a -> m (Expr a)) -> f a -> m (f a)
transformExprInM = transformBiM

freshLocal :: Name a => Type a -> Fresh (Local a)
freshLocal ty = liftM2 Local fresh (return ty)

refreshLocal :: Name a => Local a -> Fresh (Local a)
refreshLocal (Local name ty) = liftM2 Local (refresh name) (return ty)

-- | Substitution, of local variables
--
-- Since there are only rank-1 types, bound variables from lambdas and
-- case never have a forall type and thus are not applied to any types.
(//) :: Name a => Expr a -> Local a -> Expr a -> Fresh (Expr a)
e // x = transformExprM $ \ e0 -> case e0 of
    Lcl y | x == y -> freshen e
    _              -> return e0
  where
    -- Freshen lambda-bound variables, to maintain the invariant that
    -- each variable is only bound once.
    freshen = transformExprM $ \e0 -> case e0 of
      Lam args body -> do
        args' <- mapM refreshLocal args
        body' <- freshen body
        fmap (Lam args') (substMany (zip args (map Lcl args')) body')
      _ -> return e0

substMany :: Name a => [(Local a, Expr a)] -> Expr a -> Fresh (Expr a)
substMany xs e0 = foldM (\e0 (u,e) -> (e // u) e0) e0 xs

apply :: Expr a -> [Expr a] -> Expr a
apply e es@(_:_) = Builtin (At (length es)) :@: (e:es)

betaReduce :: (TransformBiM Fresh (Expr a) (f a), Name a) => f a -> Fresh (f a)
betaReduce = transformExprInM $ \e ->
  case e of
    Builtin (At _) :@: (Lam vars body:args) ->
      substMany (zip vars args) body >>= betaReduce
    _ -> return e
