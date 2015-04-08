-- A monad for keeping track of variable scope.

{-# LANGUAGE CPP, RecordWildCards, GeneralizedNewtypeDeriving, FlexibleContexts #-}
module Tip.Scope where

#include "errors.h"
import Tip hiding (globals, locals)
import Tip.Pretty
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Error
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as M
import qualified Data.Set as S
import Text.PrettyPrint
import Control.Monad.Identity
import Data.Maybe

data TypeInfo a =
    TyVarInfo
  | DatatypeInfo (Datatype a)
  | AbsTypeInfo
  deriving (Eq, Show)

data GlobalInfo a =
    FunctionInfo      (PolyType a)
  | ConstructorInfo   (Datatype a) (Constructor a)
  | ProjectorInfo     (Datatype a) (Constructor a) Int (Type a)
  | DiscriminatorInfo (Datatype a) (Constructor a)
  deriving Show

globalType :: GlobalInfo a -> PolyType a
globalType (FunctionInfo ty) = ty
globalType (ConstructorInfo dt con) = constructorType dt con
globalType (ProjectorInfo dt _ _ ty) = destructorType dt ty
globalType (DiscriminatorInfo dt _) = destructorType dt (BuiltinType Boolean)

data Scope a = Scope
  { inner   :: Set a
  , types   :: Map a (TypeInfo a)
  , locals  :: Map a (Type a)
  , globals :: Map a (GlobalInfo a) }
  deriving Show

newtype ScopeT a m b = ScopeT { unScopeT :: StateT (Scope a) (ErrorT Doc m) b }
  deriving (Functor, Applicative, Monad, MonadPlus, Alternative, MonadState (Scope a), MonadError Doc)

instance MonadTrans (ScopeT a) where
  lift = ScopeT . lift . lift

instance Error Doc where
  strMsg = text

scope :: (PrettyVar a, Ord a) => Theory a -> Scope a
scope thy = checkScope (withTheory thy get)

runScopeT :: Monad m => ScopeT a m b -> m (Either Doc b)
runScopeT (ScopeT m) = runErrorT (evalStateT m emptyScope)

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
  catchError m (\e -> throwError (sep [e, text "in context", nest 2 (pp x)]))

local :: Monad m => ScopeT a m b -> ScopeT a m b
local m = do
  s <- get
  x <- m
  put s
  return x

newScope :: Monad m => ScopeT a m b -> ScopeT a m b
newScope m = local $ do
  modify (\s -> s { inner = S.empty })
  m

newInfo :: (PrettyVar a, Ord a, Monad m) => a -> ScopeT a m ()
newInfo x = do
  s <- gets inner
  case S.member x s of
    True ->
      throwError $
        fsep [text "Name", ppVar x, text "rebound"]
    False ->
      modify (\s -> s { inner = S.insert x (inner s) })

newTyVar :: (Monad m, Ord a, PrettyVar a) => a -> ScopeT a m ()
newTyVar ty = do
  newInfo ty
  modify $ \s -> s {
    types = M.insert ty TyVarInfo (types s) }

newAbsType :: (Monad m, Ord a, PrettyVar a) => AbsType a -> ScopeT a m ()
newAbsType (AbsType ty) = do
  newInfo ty
  modify $ \s -> s {
    types = M.insert ty AbsTypeInfo (types s) }

newDatatype :: (Monad m, Ord a, PrettyVar a) => Datatype a -> ScopeT a m ()
newDatatype dt@Datatype{..} = do
  newInfo data_name
  modify $ \s -> s {
    types = M.insert data_name (DatatypeInfo dt) (types s) }
  mapM_ (newConstructor dt) data_cons

newConstructor :: (Monad m, Ord a, PrettyVar a) => Datatype a -> Constructor a -> ScopeT a m ()
newConstructor dt con@Constructor{..} = do
  mapM_ (newInfo . fst) funcs
  modify $ \s -> s {
    -- OBS entries from left argument take precedence
    globals = M.union (M.fromList funcs) (globals s) }
  where
    funcs =
      (con_name, ConstructorInfo dt con):
      (con_discrim, DiscriminatorInfo dt con):
      [(name, ProjectorInfo dt con i ty) | (i, (name, ty)) <- zip [0..] con_args]

newFunction :: (Monad m, Ord a, PrettyVar a) => AbsFunc a -> ScopeT a m ()
newFunction AbsFunc{..} = do
  newInfo abs_func_name
  modify $ \s -> s {
    globals = M.insert abs_func_name (FunctionInfo abs_func_type) (globals s) }

newLocal :: (Monad m, Ord a, PrettyVar a) => Local a -> ScopeT a m ()
newLocal Local{..} = do
  newInfo lcl_name
  modify $ \s -> s {
    locals = M.insert lcl_name lcl_type (locals s) }

withTheory :: (Monad m, Ord a, PrettyVar a) => Theory a -> ScopeT a m b -> ScopeT a m b
withTheory Theory{..} m = do
  mapM_ newDatatype thy_data_decls
  mapM_ newAbsType thy_abs_type_decls
  mapM_ (newFunction . absFunc) thy_func_decls
  mapM_ newFunction thy_abs_func_decls
  m

isType, isTyVar, isAbsType, isLocal, isGlobal :: Ord a => Scope a -> a -> Bool
isType s x = M.member x (types s)
isLocal s x = M.member x (locals s)
isGlobal s x = M.member x (globals s)
isTyVar s x = M.lookup x (types s) == Just TyVarInfo
isAbsType s x = M.lookup x (types s) == Just AbsTypeInfo

lookupType :: Ord a => Scope a -> a -> Maybe (TypeInfo a)
lookupType s x = M.lookup x (types s)

lookupLocal :: Ord a => Scope a -> a -> Maybe (Type a)
lookupLocal s x = M.lookup x (locals s)

lookupGlobal :: Ord a => Scope a -> a -> Maybe (GlobalInfo a)
lookupGlobal s x = M.lookup x (globals s)

lookupDatatype :: Ord a => Scope a -> a -> Maybe (Datatype a)
lookupDatatype s x = do
  DatatypeInfo dt <- M.lookup x (types s)
  return dt

lookupFunction :: Ord a => Scope a -> a -> Maybe (PolyType a)
lookupFunction s x = do
  FunctionInfo ty <- M.lookup x (globals s)
  return ty

lookupConstructor :: Ord a => Scope a -> a -> Maybe (Datatype a, Constructor a)
lookupConstructor s x = do
  ConstructorInfo dt con <- M.lookup x (globals s)
  return (dt, con)

lookupDiscriminator :: Ord a => Scope a -> a -> Maybe (Datatype a, Constructor a)
lookupDiscriminator s x = do
  DiscriminatorInfo dt con <- M.lookup x (globals s)
  return (dt, con)

lookupProjector :: Ord a => Scope a -> a -> Maybe (Datatype a, Constructor a, Int, Type a)
lookupProjector s x = do
  ProjectorInfo dt con i ty <- M.lookup x (globals s)
  return (dt, con, i, ty)

whichDatatype :: Ord a => Scope a -> a -> Datatype a
whichDatatype s = fromMaybe __ . lookupDatatype s
whichLocal :: Ord a => Scope a -> a -> Type a
whichLocal s = fromMaybe __ . lookupLocal s
whichGlobal :: Ord a => Scope a -> a -> GlobalInfo a
whichGlobal s = fromMaybe __ . lookupGlobal s
whichFunction :: Ord a => Scope a -> a -> PolyType a
whichFunction s = fromMaybe __ . lookupFunction s
whichConstructor :: Ord a => Scope a -> a -> (Datatype a, Constructor a)
whichConstructor s = fromMaybe __ . lookupConstructor s
whichDiscriminator :: Ord a => Scope a -> a -> (Datatype a, Constructor a)
whichDiscriminator s = fromMaybe __ . lookupDiscriminator s
whichProjector :: Ord a => Scope a -> a -> (Datatype a, Constructor a, Int, Type a)
whichProjector s = fromMaybe __ . lookupProjector s
