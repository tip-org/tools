module Main where

import Tip.HaskellFrontend

import Text.Show.Pretty hiding (Name)
import System.Environment
import qualified Data.Foldable as F
import Data.Ord

import Control.Monad

import Tip
import Tip.Fresh
import Tip.Simplify
import Tip.Lint
import Tip.Passes

import Tip.Utils.Renamer

import Tip.Pretty
import Tip.Pretty.SMT as SMT

import Text.PrettyPrint

main :: IO ()
main = do
    f:es <- getArgs
    thy <- readHaskellFile Params
      { file = f
      , include = []
      , flags = [] -- [PrintCore,PrintProps,PrintExtraIds,PrintInitialTip]
      , only = es -- []
      , extra = [] -- es
      }
    -- putStrLn (ppRender thy)
    let renamed_thy = renameWith disambigId thy
    let pipeline = freshPass $
                simplifyTheory aggressively >=> lintM "simplify0"
            >=> return . denewtype          >=> lintM "denewtype"
            >=> delambda                    >=> lintM "delambda"
            >=> simplifyTheory aggressively >=> lintM "simplify1"
            >=> commuteMatch                >=> lintM "commuteMatch"
            >=> simplifyTheory aggressively >=> lintM "simplify2"
--            >=> decase                      >=> lintM "decase"
            >=> return . removeAliases      >=> lintM "removeAliases"
            >=> return . collapseEqual      >=> lintM "collapseEqual"

    print (SMT.ppTheory (pipeline renamed_thy))

data Var = Var String | Refresh Var Int
  deriving (Show,Eq,Ord)

varMax :: Var -> Int
varMax Var{}         = 0
varMax (Refresh v i) = varMax v `max` i

instance PrettyVar Var where
  varStr (Var "")      = "x"
  varStr (Var xs)      = xs
  varStr (Refresh v i) = varStr v

disambigId :: Id -> [Var]
disambigId i = vs : [ Refresh vs x | x <- [0..] ]
  where
    vs = Var $ case varStr i of { [] -> "x"; xs -> xs }

instance Name Var where
  fresh     = refresh (Var "")
  refresh (Refresh v _) = refresh v
  refresh v@Var{}       = Refresh v `fmap` fresh

  freshNamed s = refresh (Var s)

  getUnique (Refresh _ i) = i
  getUnique Var{}         = 0

