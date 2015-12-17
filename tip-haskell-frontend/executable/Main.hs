module Main where

import Tip.HaskellFrontend

import Text.Show.Pretty hiding (Name)
import System.Environment
import qualified Data.Foldable as F
import Data.Ord

import Control.Monad

import Tip.Core
import Tip.Fresh
import Tip.Simplify
import Tip.Lint
import Tip.Passes

import Tip.Utils.Rename

import Tip.Pretty
import Tip.Pretty.SMT as SMT

import Text.PrettyPrint hiding ((<>))

import Options.Applicative

main :: IO ()
main = do
    (file,params) <-
      execParser $
        info (helper <*>
                ((,) <$> strArgument (metavar "FILENAME" <> help "Haskell file to process")
                     <*> parseParams))
          (fullDesc <>
           progDesc "Translate Haskell to TIP" <>
           header "tip-ghc - translate Haskell to TIP")
    mthy <- readHaskellFile file params
    case mthy of
      Left s -> error s
      Right thy -> do
        when (PrintInitialTheory `elem` debug_flags params) $ putStrLn (ppRender thy)
        let renamed_thy = renameWith disambigId thy
        let pipeline =
              freshPass $
                runPasses
                  [ SimplifyGently
                  , RemoveNewtype
                  , UncurryTheory
                  , CommuteMatch
                  , SimplifyGently
                  , IfToBoolOp
                  , RemoveAliases, CollapseEqual
                  , CommuteMatch
                  , SimplifyGently
                  , CSEMatch
                  , EliminateDeadCode
                  ]
        case pipeline renamed_thy of
          [thy'] -> print (SMT.ppTheory thy')
          _      -> error "tip-ghc: not one theory!"

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

