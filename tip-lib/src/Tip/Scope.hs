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
  | AbsTypeInfo Int
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

newAbsType :: (Monad m, Ord a, PrettyVar a) => AbsType a -> ScopeT a m ()
newAbsType AbsType{..} = do
  newName abs_type_name
  modify $ \s -> s {
    types = M.insert abs_type_name (AbsTypeInfo abs_type_arity) (types s) }

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

newFunction :: (Monad m, Ord a, PrettyVar a) => AbsFunc a -> ScopeT a m ()
newFunction AbsFunc{..} = do
  newName abs_func_name
  modify $ \s -> s {
    globals = M.insert abs_func_name (FunctionInfo abs_func_type) (globals s) }

newLocal :: (Monad m, Ord a, PrettyVar a) => Local a -> ScopeT a m ()
newLocal Local{..} = do
  newName lcl_name
  modify $ \s -> s {
    locals = M.insert lcl_name lcl_type (locals s) }

withTheory :: (Monad m, Ord a, PrettyVar a) => Theory a -> ScopeT a m b -> ScopeT a m b
withTheory Theory{..} m = do
  mapM_ newDatatype thy_data_decls
  mapM_ newAbsType thy_abs_type_decls
  mapM_ (newFunction . absFunc) thy_func_decls
  mapM_ newFunction thy_abs_func_decls
  m

isType, isTyVar, isAbsType, isLocal, isGlobal :: Ord a => a -> Scope a -> Bool
isType x s = M.member x (types s)
isLocal x s = M.member x (locals s)
isGlobal x s = M.member x (globals s)
isTyVar x s = M.lookup x (types s) == Just TyVarInfo
isAbsType x s = case M.lookup x (types s) of Just AbsTypeInfo{} -> True
                                             _                  -> False

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

lookupFunction :: Ord a => a -> Scope a -> Maybe (PolyType a)
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
whichFunction :: Ord a => a -> Scope a -> PolyType a
whichFunction s = fromMaybe __ . lookupFunction s
whichConstructor :: Ord a => a -> Scope a -> (Datatype a, Constructor a)
whichConstructor s = fromMaybe __ . lookupConstructor s
whichDiscriminator :: Ord a => a -> Scope a -> (Datatype a, Constructor a)
whichDiscriminator s = fromMaybe __ . lookupDiscriminator s
whichProjector :: Ord a => a -> Scope a -> (Datatype a, Constructor a, Int, Type a)
whichProjector s = fromMaybe __ . lookupProjector s
