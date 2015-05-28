module Main where

import System.Environment

import Tip.QuickSpec
import Tip.Parser (parse)

import QuickSpec (quickSpec)

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
      do (sig,_) <- theorySignature thy
         quickSpec sig
         return ()

