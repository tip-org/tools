module Main where

import System.Environment
import Text.PrettyPrint
import Tip.Parser
import Tip.Pretty.SMT as SMT
import Tip.Pretty.Why3 as Why3

main :: IO ()
main =
  do f:es <- getArgs
     s <- readFile f
     case parse s of
       Left err  -> error $ "Parse failed: " ++ err
       Right thy ->
         if "why3" `elem` es
           then putStrLn (render (Why3.ppTheory (why3VarTheory thy)))
           else putStrLn (render (SMT.ppTheory thy))

