module Main where

import Tip.HaskellFrontend
import Tip.Params
import Text.Show.Pretty
import System.Environment

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

