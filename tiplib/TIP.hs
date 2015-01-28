{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE ExplicitForAll, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
module TIP where

import Data.Generics.Geniplate
import Data.List (nub)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

data Head a
  = Gbl (Global a)
  | Builtin Builtin
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Local a = Local { lcl_id :: a, lcl_type :: Type a }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Global a = Global a (PolyType a) [Type a]
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Expr a
  = Head a :@: [Expr a]
  | Lcl (Local a)
  | Lam [Local a] (Expr a)
  | Case (Expr a) [Alt a]
  | Let (Local a) (Expr a) (Expr a)
  | Quant Quant (Local a) (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type Alt a = (Pattern a,Expr a)

data Builtin
  = Lit Lit
  | And
  | Or
  | Equal
  | At Int
  deriving (Eq,Ord,Show)

data Lit
  = Int Integer
  | Bool Bool
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
  | Integer
  | [Type a] :=>: Type a
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Function a = Function a [a] [Local a] (Type a) (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

funType :: Function a -> PolyType a
funType (Function _ tvs lcls res _) = PolyType tvs (map lcl_type lcls) res

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
  | Assert (Expr a)
  | Prove (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)
