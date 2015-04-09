{-# LANGUAGE ViewPatterns #-}
module Tip.Utils.Renamer where

import Control.Monad.State
import Control.Monad.Reader

import Data.Traversable (Traversable)
import qualified Data.Traversable as T

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Control.Arrow

type RenameM a b = ReaderT (Suggestor a b) (State (Map a b,Set b))

type Suggestor a b = a -> [b]

disambig :: (a -> String) -> Suggestor a String
disambig f (f -> x) = x : [ x ++ show (i :: Int) | i <- [2..] ]

disambig2 :: (a -> String) -> (b -> String) -> Suggestor (Either a b) String
disambig2 f _ (Left a)  = disambig f a
disambig2 _ g (Right b) = disambig g b

evalRenameM :: Ord b => Suggestor a b -> [b] -> RenameM a b r -> r
evalRenameM f block m = fst (runRenameM f block M.empty m)

runRenameM :: Ord b => Suggestor a b -> [b] -> Map a b -> RenameM a b r -> (r,Map a b)
runRenameM f block alloc m = second fst (runState (runReaderT m f) s0)
  where s0 = (alloc,S.fromList (block ++ M.elems alloc))

insert :: (Ord a,Ord b) => a -> RenameM a b b
insert n = go =<< asks ($ n)
  where
    go (s:ss) = do
        u <- gets snd
        if s `S.member` u then go ss else do
            modify (M.insert n s *** S.insert s)
            return s
    go [] = error "ran out of names!?"

insertMany :: (Ord a,Ord b) => [a] -> RenameM a b [b]
insertMany = mapM insert

lkup :: (Ord a,Ord b) => a -> RenameM a b b
lkup n = do
    m_s <- gets (M.lookup n . fst)
    case m_s of
        Just s  -> return s
        Nothing -> insert n

rename :: (Ord a,Ord b,Traversable t) => t a -> RenameM a b (t b)
rename = T.mapM lkup

renameWith :: (Ord a,Ord b,Traversable t) => Suggestor a b -> t a -> t b
renameWith = renameWithBlocks []

renameWithBlocks :: (Ord a,Ord b,Traversable t) => [b] -> Suggestor a b -> t a -> t b
renameWithBlocks bs f = evalRenameM f bs . rename

