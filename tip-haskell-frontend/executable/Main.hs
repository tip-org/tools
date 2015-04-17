module Main where

import Tip.HaskellFrontend
import Tip.Params
import Text.Show.Pretty hiding (Name)
import System.Environment
import qualified Data.Foldable as F
import Data.Ord

import Control.Monad

import Tip
import Tip.AxiomatizeFuncdefs
import Tip.Id
import Tip.CommuteMatch
import Tip.Decase
import Tip.Delambda
import Tip.Denewtype
import Tip.Lift
import Tip.Fresh
import Tip.Utils.Renamer
import Tip.Pretty
import Tip.Pretty.SMT as SMT
import Tip.EqualFunctions
import Tip.Simplify
import Tip.Lint

import Text.PrettyPrint

main :: IO ()
main = do
    f:es <- getArgs
    thy <- readHaskellFile Params
      { file = f
      , include = []
      , flags = [] -- [PrintCore,PrintProps,PrintExtraIds]
      , only = es -- []
      , extra = []
      , extra_trans = [] -- es
      }
    -- putStrLn (ppRender thy)
    let rnm = renameWith disambigId thy
    let dlm = freshPass ( return
                        -- . lint "decase" <=< decase
                        . lint "simplify2" <=< simplifyTheory aggressively
                        . lint "commuteMatch" <=< commuteMatch
                        . lint "simplify1" <=< simplifyTheory aggressively
                        . lint "delambda" <=< delambda
                        . lint "denewtype" <=< return . denewtype
                        . lint "simplify0" <=< simplifyTheory aggressively)
                        rnm
    {- letLift =<< lambdaLift =<< -} --
    -- putStrLn "\n == After delambda and defunctionalization:"
    -- putStrLn (ppRender dlm)
    -- putStrLn "\n == After collapse equal:"
    print (SMT.ppTheory (lint "collapseEqual" (collapseEqual (lint "removeAliases" (removeAliases dlm)))))
    -- putStrLn "\n == After axiomatization:"
    -- let after_ax = axiomatizeLambdas (collapseEqual dlm)
    -- putStrLn (ppRender after_ax)
    -- putStrLn "\n == After commute match:"
    -- let commute = runFreshFrom (maximumOn varMax after_ax)
    --                            (commuteMatch after_ax)
    -- putStrLn (ppRender commute)
    -- putStrLn "\n == After axiomatize function definitions:"
    -- let ax_fns = axiomatizeFuncdefs commute
    -- putStrLn (ppRender ax_fns)

data Var = Var String | Refresh Var Int
  deriving (Show,Eq,Ord)

varMax :: Var -> Int
varMax Var{}         = 0
varMax (Refresh v i) = varMax v `max` i

instance PrettyVar Var where
  varStr (Var "")      = "x"
  varStr (Var xs)      = xs
  varStr (Refresh v i) = varStr v ++ show i

disambigId :: Id -> [Var]
disambigId i = vs : [ Refresh vs x | x <- [0..] ]
  where
    vs = Var $ case ppId i of { [] -> "x"; xs -> xs }

instance Name Var where
  fresh     = refresh (Var "")
  refresh (Refresh v _) = refresh v
  refresh v@Var{}       = Refresh v `fmap` fresh

  getUnique (Refresh _ i) = i
  getUnique Var{}         = 0

