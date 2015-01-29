{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE ExplicitForAll, FlexibleContexts, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
module Tip where

import Tip.Fresh
import Tip.Utils
import Data.Generics.Geniplate
import Data.List (nub, (\\))
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Control.Monad
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)

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

data Quant = Forall | Exists
  deriving (Eq,Ord,Show)

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
  = FuncDecl (Function a)
  | DataDecl (Datatype a)
  | Assert (Expr a)
  | Prove (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instanceUniverseBi [t| forall a . (Expr a,Expr a) |]
instanceUniverseBi [t| forall a . (Function a,Expr a) |]
instanceUniverseBi [t| forall a . (Expr a,Pattern a) |]
instanceUniverseBi [t| forall a . (Expr a,Local a) |]
instanceTransformBi [t| forall a . (Expr a,Expr a) |]
instanceTransformBi [t| forall a . (Expr a,Function a) |]
instanceTransformBi [t| forall a . (Pattern a,Expr a) |]
instanceTransformBi [t| forall a . (Local a,Expr a) |]
instance Monad m => TransformBiM m (Expr a) (Expr a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Expr a) (Function a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Function a -> m (Function a) |])
instance Monad m => TransformBiM m (Pattern a) (Expr a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Pattern a -> m (Pattern a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Local a) (Expr a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Local a -> m (Local a)) -> Expr a -> m (Expr a) |])

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
substMany xs e0 = foldM (\e0 (u,e) -> (e // u) e0) e0 xs

apply :: Expr a -> [Expr a] -> Expr a
apply e es@(_:_) = Builtin (At (length es)) :@: (e:es)

betaReduce :: (TransformBiM Fresh (Expr a) (f a), Name a) => f a -> Fresh (f a)
betaReduce = transformExprInM $ \e ->
  case e of
    Builtin (At _) :@: (Lam vars body:args) ->
      substMany (zip vars args) body >>= betaReduce
    _ -> return e
