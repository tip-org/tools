-- | the abstract syntax
{-# LANGUAGE RecordWildCards #-}
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
  -- ^ Function application: always perfectly saturated.
  --   Lambdas and locals are applied with 'At' as head.
  | Lcl (Local a)
  | Lam [Local a] (Expr a)
  -- Merge with Quant?
  | Match (Expr a) [Case a]
  -- ^ The default case comes first if there is one
  | Let (Local a) (Expr a) (Expr a)
  -- ^ @Let (Local x t) b e@ = @(let ((l x)) b e)@
  -- Unlike SMT-LIB, this does not accept a list of bound
  -- variable-/expression-pairs. Fix?
  | Quant QuantInfo Quant [Local a] (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Quant = Forall | Exists
  deriving (Eq,Ord,Show)

data QuantInfo = NoInfo | QuantIH Int
  deriving (Eq,Ord,Show)

data Case a = Case { case_pat :: Pattern a, case_rhs :: Expr a }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Builtin
  = At
  | Lit Lit
  | And
  | Or
  | Not
  | Implies
  | Equal
  | Distinct
  | IntAdd
  | IntSub
  | IntMul
  | IntDiv
  | IntMod
  | IntGt
  | IntGe
  | IntLt
  | IntLe
  deriving (Eq,Ord,Show)

intBuiltin :: Builtin -> Bool
intBuiltin b = b `elem` [IntAdd,IntSub,IntMul,IntDiv,IntMod,IntGt,IntGe,IntLt,IntLe]

litBuiltin :: Builtin -> Bool
litBuiltin Lit{} = True
litBuiltin _     = False

eqRelatedBuiltin :: Builtin -> Bool
eqRelatedBuiltin b = b `elem` [Equal,Distinct]

logicalBuiltin :: Builtin -> Bool
logicalBuiltin b = b `elem` [And,Or,Implies,Equal,Distinct,Not]

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
data PolyType a =
  PolyType
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
  | BuiltinType BuiltinType
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data BuiltinType
  = Integer | Boolean
  deriving (Eq,Ord,Show)

  -- If this definition is imported from some source file, or local to this file.
data Source =
      Imported (String, String)
  deriving (Eq,Ord,Show)


data Function a = Function
  { func_name :: a
  , func_tvs  :: [a]
  , func_args :: [Local a]
  , func_res  :: Type a
  , func_body :: Expr a
  , func_source :: Maybe Source
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Uninterpreted function
data Signature a = Signature
  { sig_name :: a
  , sig_type :: PolyType a
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Uninterpreted sort
data Sort a = Sort
  { sort_name :: a
  , sort_tvs  :: [a] }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Data definition
data Datatype a = Datatype
  { data_name :: a
  , data_tvs  :: [a]
  , data_cons :: [Constructor a]
  , data_source    :: Maybe Source
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Constructor a = Constructor
  { con_name    :: a
  -- ^ Constructor name (e.g. @Cons@)
  , con_discrim :: a
  -- ^ Discriminator name (e.g. @is-Cons@)
  , con_args    :: [(a,Type a)]
  -- ^ Argument types names of their projectors
  --   (e.g. [(@head@,a),(@tail@,List a)])
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Theory a = Theory
  { thy_datatypes   :: [Datatype a]
  , thy_sorts       :: [Sort a]
  , thy_sigs        :: [Signature a]
  , thy_funcs       :: [Function a]
  , thy_asserts     :: [Formula a]
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

emptyTheory :: Theory a
emptyTheory = Theory [] [] [] [] []

joinTheories :: Theory a -> Theory a -> Theory a
joinTheories (Theory a o e u i) (Theory s n t h d) = Theory (a++s) (o++n) (e++t) (u++h) (i++d)

instance Monoid (Theory a) where
  mempty  = emptyTheory
  mappend = joinTheories

data Formula a = Formula
  { fm_role :: Role
  , fm_name :: Maybe a -- force all formulas to have a name?
  , fm_source :: Maybe Source
  , fm_info :: Info a
  , fm_tvs  :: [a]
  -- ^ top-level quantified type variables
  , fm_body :: Expr a
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Info a
  = Definition a
  | IH Int
  | Lemma Int
  | Projection a
  | DataDomain a
  | DataProjection a
  | DataDistinct a
  | Defunction a
  | UserAsserted
  | Unknown
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Role = Assert | Prove
  deriving (Eq,Ord,Show)

data IndScheme a =
    Structural (Datatype a)
  | Recursion (Function a)
  | OtherScheme a
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data ProofPlan a =
    Direct [Formula a] -- proof without induction by e.g. FO prover, using listed lemmas.
  | Induction (IndScheme a)
              [Local a] -- vars to do ind on
              [Formula a] -- lemmas used
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- * Other views of theories

-- | The different kinds of declarations in a 'Theory'.
data Decl a
    = DataDecl (Datatype a)
    | SortDecl (Sort a)
    | SigDecl (Signature a)
    | FuncDecl (Function a)
    | AssertDecl (Formula a) -- rename to FormulaDecl?
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | 'Decl'arations in a 'Theory'
theoryDecls :: Theory a -> [Decl a]
theoryDecls (Theory{..}) =
    map DataDecl thy_datatypes ++
    map SortDecl thy_sorts ++
    map SigDecl thy_sigs ++
    map FuncDecl thy_funcs ++
    map AssertDecl thy_asserts

-- | Assemble a 'Theory' from some 'Decl'arations
declsToTheory :: [Decl a] -> Theory a
declsToTheory ds = Theory
    { thy_datatypes = [ d | DataDecl d   <- ds ]
    , thy_sorts     = [ d | SortDecl d   <- ds ]
    , thy_sigs      = [ d | SigDecl d    <- ds ]
    , thy_funcs     = [ d | FuncDecl d   <- ds ]
    , thy_asserts   = [ d | AssertDecl d <- ds ]
    }

declsPass :: ([Decl a] -> [Decl b]) -> Theory a -> Theory b
declsPass k = declsToTheory . k . theoryDecls

-- Instances

instanceUniverseBi [t| forall a . (Expr a,Expr a) |]
instanceUniverseBi [t| forall a . (Function a,Expr a) |]
instanceUniverseBi [t| forall a . (Function a,Global a) |]
instanceUniverseBi [t| forall a . (Function a,Type a) |]
instanceUniverseBi [t| forall a . (Datatype a,Type a) |]
instanceUniverseBi [t| forall a . (Expr a,Pattern a) |]
instanceUniverseBi [t| forall a . (Expr a,Local a) |]
instanceUniverseBi [t| forall a . (Expr a,Global a) |]
instanceUniverseBi [t| forall a . (Theory a,Expr a) |]
instanceUniverseBi [t| forall a . (Theory a,Type a) |]
instanceUniverseBi [t| forall a . (Type a,Type a) |]
instanceUniverseBi [t| forall a . (Theory a,Constructor a) |]
instanceUniverseBi [t| forall a . (Theory a,Global a) |]
instanceUniverseBi [t| forall a . (Theory a,Local a) |]
instanceUniverseBi [t| forall a . (Theory a,Builtin) |]
instanceTransformBi [t| forall a . (Expr a,Expr a) |]
instanceTransformBi [t| forall a . (a,Expr a) |]
instanceTransformBi [t| forall a . (a,Formula a) |]
instanceTransformBi [t| forall a . (Expr a,Function a) |]
instanceTransformBi [t| forall a . (Expr a,Theory a) |]
instanceTransformBi [t| forall a . (Head a,Expr a) |]
instanceTransformBi [t| forall a . (Head a,Theory a) |]
instanceTransformBi [t| forall a . (Local a,Expr a) |]
instanceTransformBi [t| forall a . (Pattern a,Expr a) |]
instanceTransformBi [t| forall a . (Pattern a,Theory a) |]
instanceTransformBi [t| forall a . (Type a,Theory a) |]
instanceTransformBi [t| forall a . (Global a,Theory a) |]
instanceTransformBi [t| forall a . (Type a,Decl a) |]
instanceTransformBi [t| forall a . (Type a,Expr a) |]
instanceTransformBi [t| forall a . (Type a,Type a) |]
instance Monad m => TransformBiM m (Expr a) (Expr a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Expr a) (Function a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Function a -> m (Function a) |])
instance Monad m => TransformBiM m (Pattern a) (Expr a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Pattern a -> m (Pattern a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Local a) (Expr a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Local a -> m (Local a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Expr a) (Theory a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Theory a -> m (Theory a) |])
instance Monad m => TransformBiM m (Expr a) (Formula a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Formula a -> m (Formula a) |])
instance Monad m => TransformBiM m (Type a) (Type a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Type a -> m (Type a)) -> Type a -> m (Type a) |])
instance Monad m => TransformBiM m (Type a) (Theory a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Type a -> m (Type a)) -> Theory a -> m (Theory a) |])
instance Monad m => TransformBiM m (Function a) (Theory a) where
  {-# INLINE transformBiM #-}
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

transformTypeInExpr :: (Type a -> Type a) -> Expr a -> Expr a
transformTypeInExpr =
  $(genTransformBiT' [[t|PolyType|]] [t|forall a. (Type a -> Type a) -> Expr a -> Expr a|])

transformTypeInDecl :: (Type a -> Type a) -> Decl a -> Decl a
transformTypeInDecl =
  $(genTransformBiT' [[t|PolyType|]] [t|forall a. (Type a -> Type a) -> Decl a -> Decl a|])
