module Main where

import System.Environment

import Tip.QuickSpec
import Tip.Parser (parse)

import qualified Tip.Pretty.SMT as SMT

main :: IO ()
main =
  do args <- getArgs
     case args of
        "-":es -> handle es =<< getContents
        f:es   -> handle es =<< readFile f
        es     -> handle es =<< getContents

handle :: [String] -> String -> IO ()
handle es s =
  case parse s of
    Left err  -> error $ "Parse failed: " ++ err
    Right thy ->
      do thy' <- exploreTheory thy
         print (SMT.ppTheory thy')

