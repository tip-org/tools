module Main where

import Tip.HaskellFrontend
import Tip.Params
import Text.Show.Pretty hiding (Name)
import System.Environment

import Tip.Id
import Tip.Delambda
import Tip.Fresh
import Tip.Utils.Renamer

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
    putStrLn (ppShow thy)
    let thy' = renameWith disambigId thy
    putStrLn (ppShow thy')
    let dlm = runFresh (delambda thy')
    putStrLn (ppShow dlm)

data Var = Var String | Refresh Var Int
  deriving (Show,Eq,Ord)

disambigId :: Id -> [Var]
disambigId i = vs : [ Refresh vs x | x <- [0..] ]
  where
    vs = Var $ case ppId i of { [] -> "?"; xs -> xs }

instance Name Var where
  fresh     = refresh (Var "")
  refresh v = Refresh v `fmap` fresh

