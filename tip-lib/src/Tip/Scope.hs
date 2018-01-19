-- | A monad for keeping track of variable scope.
{-# LANGUAGE CPP, RecordWildCards, GeneralizedNewtypeDeriving, FlexibleContexts #-}
module Tip.Scope where

#include "errors.h"
import Tip.Core hiding (globals, locals)
import Tip.Pretty
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as M
import qualified Data.Set as S
import Text.PrettyPrint
import Control.Monad.Identity
import Data.Maybe

-- | The scope of a theory
scope :: (PrettyVar a, Ord a) => Theory a -> Scope a
scope thy = checkScope (withTheory thy get)

data Scope a = Scope
  { inner   :: Set a
  , types   :: Map a (TypeInfo a)
  , locals  :: Map a (Type a)
  , globals :: Map a (GlobalInfo a) }
  deriving Show

-- * Querying the scope

data TypeInfo a =
    TyVarInfo
  | DatatypeInfo (Datatype a)
  | SortInfo (Sort a)
  deriving (Eq, Show)

instance HasAttr (TypeInfo a) where
  getAttrs TyVarInfo = []
  getAttrs (DatatypeInfo dt) = getAttrs dt
  getAttrs (SortInfo s) = getAttrs s
  putAttrs _ TyVarInfo = TyVarInfo
  putAttrs attrs (DatatypeInfo dt) = DatatypeInfo (putAttrs attrs dt)
  putAttrs attrs (SortInfo s) = SortInfo (putAttrs attrs s)

data GlobalInfo a =
    FunctionInfo      (Signature a)
  | ConstructorInfo   (Datatype a) (Constructor a)
  | ProjectorInfo     (Datatype a) (Constructor a) Int (Type a)
  | DiscriminatorInfo (Datatype a) (Constructor a)
  deriving Show

instance HasAttr (GlobalInfo a) where
  getAttrs (FunctionInfo fun) = getAttrs fun
  getAttrs (ConstructorInfo _ con) = getAttrs con
  -- Projectors and discriminator don't have their own attributes.
  getAttrs ProjectorInfo{} = []
  getAttrs DiscriminatorInfo{} = []
  putAttrs attrs (FunctionInfo fun) =
    FunctionInfo (putAttrs attrs fun)
  putAttrs attrs (ConstructorInfo dt con) =
    ConstructorInfo dt (putAttrs attrs con)
  putAttrs _ x = x

globalType :: GlobalInfo a -> PolyType a
globalType (FunctionInfo ty) = sig_type ty
globalType (ConstructorInfo dt con) = constructorType dt con
globalType (ProjectorInfo dt _ _ ty) = destructorType dt ty
globalType (DiscriminatorInfo dt _) = destructorType dt (BuiltinType Boolean)

dataTypeGlobals :: (PrettyVar a,Ord a) => Datatype a -> [(a,GlobalInfo a)]
dataTypeGlobals dt = M.toList (globals (scope emptyTheory { thy_datatypes = [dt] }))

isType, isTyVar, isSort, isLocal, isGlobal :: Ord a => a -> Scope a -> Bool
isType x s = M.member x (types s)
isLocal x s = M.member x (locals s)
isGlobal x s = M.member x (globals s)
isTyVar x s = M.lookup x (types s) == Just TyVarInfo
isSort x s = case M.lookup x (types s) of Just SortInfo{} -> True
                                          _               -> False

lookupType :: Ord a => a -> Scope a -> Maybe (TypeInfo a)
lookupType x s = M.lookup x (types s)

lookupLocal :: Ord a => a -> Scope a -> Maybe (Type a)
lookupLocal x s = M.lookup x (locals s)

lookupGlobal :: Ord a => a -> Scope a -> Maybe (GlobalInfo a)
lookupGlobal x s = M.lookup x (globals s)

lookupDatatype :: Ord a => a -> Scope a -> Maybe (Datatype a)
lookupDatatype x s = do
  DatatypeInfo dt <- M.lookup x (types s)
  return dt

lookupFunction :: Ord a => a -> Scope a -> Maybe (Signature a)
lookupFunction x s = do
  FunctionInfo ty <- M.lookup x (globals s)
  return ty

lookupConstructor :: Ord a => a -> Scope a -> Maybe (Datatype a, Constructor a)
lookupConstructor x s = do
  ConstructorInfo dt con <- M.lookup x (globals s)
  return (dt, con)

lookupDiscriminator :: Ord a => a -> Scope a -> Maybe (Datatype a, Constructor a)
lookupDiscriminator x s = do
  DiscriminatorInfo dt con <- M.lookup x (globals s)
  return (dt, con)

lookupProjector :: Ord a => a -> Scope a -> Maybe (Datatype a, Constructor a, Int, Type a)
lookupProjector x s = do
  ProjectorInfo dt con i ty <- M.lookup x (globals s)
  return (dt, con, i, ty)

whichDatatype :: Ord a => a -> Scope a -> Datatype a
whichDatatype s = fromMaybe __ . lookupDatatype s
whichLocal :: Ord a => a -> Scope a -> Type a
whichLocal s = fromMaybe __ . lookupLocal s
whichGlobal :: Ord a => a -> Scope a -> GlobalInfo a
whichGlobal s = fromMaybe __ . lookupGlobal s
whichFunction :: Ord a => a -> Scope a -> Signature a
whichFunction s = fromMaybe __ . lookupFunction s
whichConstructor :: Ord a => a -> Scope a -> (Datatype a, Constructor a)
whichConstructor s = fromMaybe __ . lookupConstructor s
whichDiscriminator :: Ord a => a -> Scope a -> (Datatype a, Constructor a)
whichDiscriminator s = fromMaybe __ . lookupDiscriminator s
whichProjector :: Ord a => a -> Scope a -> (Datatype a, Constructor a, Int, Type a)
whichProjector s = fromMaybe __ . lookupProjector s

-- * The scope monad

newtype ScopeT a m b = ScopeT { unScopeT :: StateT (Scope a) (ExceptT Doc m) b }
  deriving (Functor, Applicative, Monad, MonadPlus, Alternative, MonadState (Scope a), MonadError Doc)

instance MonadTrans (ScopeT a) where
  lift = ScopeT . lift . lift

runScopeT :: Monad m => ScopeT a m b -> m (Either Doc b)
runScopeT (ScopeT m) = runExceptT (evalStateT m emptyScope)

checkScopeT :: Monad m => ScopeT a m b -> m b
checkScopeT m = runScopeT m >>= check
  where
    check (Left err) = fail (show err)
    check (Right x)  = return x

type ScopeM a = ScopeT a Identity

runScope :: ScopeM a b -> Either Doc b
runScope = runIdentity . runScopeT

checkScope :: ScopeM a b -> b
checkScope = runIdentity . checkScopeT

emptyScope :: Scope a
emptyScope = Scope S.empty M.empty M.empty M.empty

inContext :: Pretty a => a -> ScopeM b c -> ScopeM b c
inContext x m =
  catchError m (\e -> throwError (vcat [sep [text "In context:", nest 2 (pp x)], text "", e]))

local :: Monad m => ScopeT a m b -> ScopeT a m b
local m = do
  s <- get
  x <- m
  put s
  return x

-- * Adding things to the scope in the scope monad

newScope :: Monad m => ScopeT a m b -> ScopeT a m b
newScope m = local $ do
  modify (\s -> s { inner = S.empty })
  m

newName :: (PrettyVar a, Ord a, Monad m) => a -> ScopeT a m ()
newName x = do
  s <- gets inner
  case S.member x s of
    True ->
      throwError $
        fsep [text "Name", ppVar x, text "rebound"]
    False ->
      modify (\s -> s { inner = S.insert x (inner s) })

newTyVar :: (Monad m, Ord a, PrettyVar a) => a -> ScopeT a m ()
newTyVar ty = do
  newName ty
  modify $ \s -> s {
    types = M.insert ty TyVarInfo (types s) }

newSort :: (Monad m, Ord a, PrettyVar a) => Sort a -> ScopeT a m ()
newSort sort@Sort{..} = do
  newName sort_name
  modify $ \s -> s {
    types = M.insert sort_name (SortInfo sort) (types s) }

newDatatype :: (Monad m, Ord a, PrettyVar a) => Datatype a -> ScopeT a m ()
newDatatype dt@Datatype{..} = do
  newName data_name
  modify $ \s -> s {
    types = M.insert data_name (DatatypeInfo dt) (types s) }
  mapM_ (newConstructor dt) data_cons

newConstructor :: (Monad m, Ord a, PrettyVar a) => Datatype a -> Constructor a -> ScopeT a m ()
newConstructor dt con@Constructor{..} = do
  mapM_ (newName . fst) funcs
  modify $ \s -> s {
    -- OBS entries from left argument take precedence
    globals = M.union (M.fromList funcs) (globals s) }
  where
    funcs =
      (con_name, ConstructorInfo dt con):
      (con_discrim, DiscriminatorInfo dt con):
      [(name, ProjectorInfo dt con i ty) | (i, (name, ty)) <- zip [0..] con_args]

newFunction :: (Monad m, Ord a, PrettyVar a) => Signature a -> ScopeT a m ()
newFunction sig@Signature{..} = do
  newName sig_name
  modify $ \s -> s {
    globals = M.insert sig_name (FunctionInfo sig) (globals s) }

newLocal :: (Monad m, Ord a, PrettyVar a) => Local a -> ScopeT a m ()
newLocal Local{..} = do
  newName lcl_name
  modify $ \s -> s {
    locals = M.insert lcl_name lcl_type (locals s) }

-- | Add everything in a theory
withTheory :: (Monad m, Ord a, PrettyVar a) => Theory a -> ScopeT a m b -> ScopeT a m b
withTheory Theory{..} m = do
  mapM_ newDatatype thy_datatypes
  mapM_ newSort thy_sorts
  mapM_ (newFunction . signature) thy_funcs
  mapM_ newFunction thy_sigs
  m

