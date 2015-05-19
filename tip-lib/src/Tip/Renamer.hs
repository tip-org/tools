{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Renamer(renameAvoiding,RenamedId(..)) where

#include "errors.h"
import Data.Char (isDigit)
import Tip hiding (globals)
import Tip.Scope
import Tip.Pretty
import Tip.Utils.Renamer
import Data.Traversable (Traversable)
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.Map as M

-- | The representation of renamed Ids.
newtype RenamedId = RenamedId String
  deriving (Eq,Ord,Show)

instance PrettyVar RenamedId where
  varStr (RenamedId x) = x

data TwoStage a = Remain a | Renamed String
 deriving (Eq,Ord)

instance PrettyVar a => Show (TwoStage a) where
  show (Remain x)  = "Remain " ++ varStr x
  show (Renamed s) = "Renamed " ++ s

renameSome
  :: (Traversable t,Ord a,PrettyVar a)
  => (a -> Bool) -> [String] -> (a -> [String]) -> t a -> t (TwoStage a)
renameSome p_rename kwds mk_name =
  renameWithBlocks
    (map Renamed kwds)
    (\ v ->
      if p_rename v then map Renamed (mk_name v)
                    else Remain v:__)

renameRest
  :: (Traversable t,Ord a,PrettyVar a)
  => [String] -> (a -> [String]) -> t (TwoStage a) -> t RenamedId
renameRest kwds mk_name =
  renameWithBlocks
    (map RenamedId kwds)
    (\ v ->
       case v of
         Renamed s -> RenamedId s:__
         Remain a  -> map RenamedId (mk_name a))

-- | Renames a theory
renameAvoiding :: forall a . (Ord a,PrettyVar a) =>
       [String]         -- ^ Keywords to avoid
    -> (Char -> String) -- ^ Escaping
    -> Theory a         -- ^ Theory to be renamed
    -> Theory RenamedId -- ^ The renamed theory
renameAvoiding kwds repl thy
   = mapDecls (renameRest kwds (filter (`notElem` assigned_gbl_names) . disambig rn)) first_pass
 where
  first_pass :: Theory (TwoStage a)
  first_pass = renameSome (`elem` gbls0) kwds (disambig rn) thy
    where gbls0 = M.keys (globals (scope thy)) ++ M.keys (types (scope thy))

  assigned_gbl_names   = [ s | Renamed s <- F.toList first_pass ]

  rn :: a -> String
  rn = concatMap repl . varStr

