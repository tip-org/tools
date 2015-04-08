module Main where

import System.Environment
import Text.PrettyPrint
import Tip.Parser
import Tip.Pretty.SMT

main :: IO ()
main =
  do f:es <- getArgs
     s <- readFile f
     case parse s of
       Left err  -> error $ "Parse failed: " ++ err
       Right thy -> putStrLn (render (ppTheory thy))

