{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE ExplicitForAll, FlexibleContexts, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
module Tip.Types where

import Data.Generics.Geniplate
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Monoid

data Head a
  = Gbl (Global a)
  | Builtin Builtin
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Local a = Local { lcl_name :: a, lcl_type :: Type a }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Global a = Global
  { gbl_name      :: a
  , gbl_type      :: PolyType a
  , gbl_args      :: [Type a]
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

infix 5 :@:

data Expr a
  = Head a :@: [Expr a]
  | Lcl (Local a)
  | Lam [Local a] (Expr a)
  | Match (Expr a) [Case a]
  | Let (Local a) (Expr a) (Expr a)
  | Quant QuantInfo Quant [Local a] (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Quant = Forall | Exists
  deriving (Eq,Ord,Show)

data QuantInfo = NoInfo
  deriving (Eq,Ord,Show)

data Case a = Case { case_pat :: Pattern a, case_rhs :: Expr a }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Builtin
  = At Int
  | Lit Lit
  | And
  | Or
  | Not
  | Implies
  | Equal    -- might have to add a (Type a) argument later
  | Distinct
  | IntAdd
  | IntSub
  | IntMul
  | IntGt
  | IntGe
  | IntLt
  | IntLe
  deriving (Eq,Ord,Show)

logicalBuiltin :: Builtin -> Bool
logicalBuiltin b = b `elem` [And,Or,Implies,Equal,Distinct,Not]

data Lit
  = Int Integer
  | Bool Bool
  | String String -- Not really here but might come from GHC
  deriving (Eq,Ord,Show)

-- | Patterns in branches
data Pattern a
    -- Default should be first if there is a default case
  = Default
  | ConPat { pat_con  :: Global a, pat_args :: [Local a] }
  | LitPat Lit
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Polymorphic types
data PolyType a =
  PolyType
    { polytype_tvs  :: [a]
    , polytype_args :: [Type a]
    , polytype_res  :: Type a
    }
  | NoPolyType
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Types
data Type a
  = TyVar a
  | TyCon a [Type a]
  | [Type a] :=>: Type a
  | BuiltinType BuiltinType
  | NoType
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data BuiltinType
  = Integer | Boolean
  deriving (Eq,Ord,Show)

data Function a = Function
  { func_name :: a
  , func_tvs  :: [a]
  , func_args :: [Local a]
  , func_res  :: Type a
  , func_body :: Expr a
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data AbsFunc a = AbsFunc
  { abs_func_name :: a
  , abs_func_type :: PolyType a
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data AbsType a = AbsType a
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Data definition
data Datatype a = Datatype
  { data_name :: a
  , data_tvs  :: [a]
  , data_cons :: [Constructor a]
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Constructor a = Constructor
  { con_name    :: a
  , con_discrim :: a
  , con_args    :: [(a,Type a)]
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Theory a = Theory
  { thy_data_decls     :: [Datatype a] -- thy_datatypes
  , thy_abs_type_decls :: [AbsType a]  -- thy_sorts     and Sort?
  , thy_abs_func_decls :: [AbsFunc a]  -- thy_abs_sigs  and Abstract? (Or uninterpreted)
  , thy_func_decls     :: [Function a] -- thy_funcs
  , thy_form_decls     :: [Formula a]  -- thy_forms
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

emptyTheory :: Theory a
emptyTheory = Theory [] [] [] [] []

joinTheories :: Theory a -> Theory a -> Theory a
joinTheories (Theory a o e u i) (Theory s n t h d) = Theory (a++s) (o++n) (e++t) (u++h) (i++d)

instance Monoid (Theory a) where
  mempty  = emptyTheory
  mappend = joinTheories

data Formula a = Formula Role [a] {- ^ type variables -} (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Role = Assert | Prove
  deriving (Eq,Ord,Show)

instanceUniverseBi [t| forall a . (Expr a,Expr a) |]
instanceUniverseBi [t| forall a . (Function a,Expr a) |]
instanceUniverseBi [t| forall a . (Function a,Global a) |]
instanceUniverseBi [t| forall a . (Function a,Type a) |]
instanceUniverseBi [t| forall a . (Datatype a,Type a) |]
instanceUniverseBi [t| forall a . (Expr a,Pattern a) |]
instanceUniverseBi [t| forall a . (Expr a,Local a) |]
instanceUniverseBi [t| forall a . (Expr a,Global a) |]
instanceUniverseBi [t| forall a . (Theory a,Expr a) |]
instanceUniverseBi [t| forall a . (Type a,Type a) |]
instanceUniverseBi [t| forall a . (Theory a,Constructor a) |]
instanceTransformBi [t| forall a . (Expr a,Expr a) |]
instanceTransformBi [t| forall a . (Expr a,Function a) |]
instanceTransformBi [t| forall a . (Expr a,Theory a) |]
instanceTransformBi [t| forall a . (Head a,Expr a) |]
instanceTransformBi [t| forall a . (Head a,Theory a) |]
instanceTransformBi [t| forall a . (Local a,Expr a) |]
instanceTransformBi [t| forall a . (Pattern a,Expr a) |]
instanceTransformBi [t| forall a . (Pattern a,Theory a) |]
instanceTransformBi [t| forall a . (Type a,Theory a) |]
instanceTransformBi [t| forall a . (Type a,Type a) |]
instance Monad m => TransformBiM m (Expr a) (Expr a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Expr a) (Function a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Function a -> m (Function a) |])
instance Monad m => TransformBiM m (Pattern a) (Expr a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Pattern a -> m (Pattern a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Local a) (Expr a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Local a -> m (Local a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Expr a) (Theory a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Theory a -> m (Theory a) |])
instance Monad m => TransformBiM m (Type a) (Type a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Type a -> m (Type a)) -> Type a -> m (Type a) |])
instance Monad m => TransformBiM m (Function a) (Theory a) where
  transformBiM = $(genTransformBiM' [t| forall m a . (Function a -> m (Function a)) -> Theory a -> m (Theory a) |])

transformExpr :: (Expr a -> Expr a) -> Expr a -> Expr a
transformExpr = transformBi

transformExprM :: Monad m => (Expr a -> m (Expr a)) -> Expr a -> m (Expr a)
transformExprM = transformBiM

transformExprIn :: TransformBi (Expr a) (f a) => (Expr a -> Expr a) -> f a -> f a
transformExprIn = transformBi

transformExprInM :: TransformBiM m (Expr a) (f a) => (Expr a -> m (Expr a)) -> f a -> m (f a)
transformExprInM = transformBiM

transformType :: (Type a -> Type a) -> Type a -> Type a
transformType = transformBi
