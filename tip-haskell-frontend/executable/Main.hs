module Main where

import Tip.HaskellFrontend
import Tip.Params
import Text.Show.Pretty hiding (Name)
import System.Environment

import Tip.Id
import Tip.Delambda
import Tip.Lambda
import Tip.Fresh
import Tip.Utils.Renamer
import Tip.Pretty
import Tip.EqualFunctions

import Text.PrettyPrint

main :: IO ()
main = do
    f:es <- getArgs
    thy <- readHaskellFile Params
      { file = f
      , include = []
      , flags = [PrintCore,PrintProps,PrintExtraIds]
      , only = []
      , extra = []
      , extra_trans = es
      }
    putStrLn (ppRender thy)
    let dlm = runFresh (defunctionalize =<< delambda (renameWith disambigId thy))
    putStrLn "After delambda and defunctionalization:"
    putStrLn (ppRender dlm)
    putStrLn "After collapse equal:"
    putStrLn (ppRender (collapseEqual dlm))

data Var = Var String | Refresh Var Int
  deriving (Show,Eq,Ord)

instance Pretty Var where
  pp (Var "") = text "x"
  pp (Var xs) = text xs
  pp (Refresh v i) = pp v <> int i

disambigId :: Id -> [Var]
disambigId i = vs : [ Refresh vs x | x <- [0..] ]
  where
    vs = Var $ case ppId i of { [] -> "x"; xs -> xs }

instance Name Var where
  fresh     = refresh (Var "")
  refresh v = Refresh v `fmap` fresh

