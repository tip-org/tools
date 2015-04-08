module Main where

import System.Environment
import Text.PrettyPrint
import Tip.Parser
import Tip.Pretty.SMT as SMT
import Tip.Pretty.Why3 as Why3
import Tip.Lint

main :: IO ()
main =
  do f:es <- getArgs
     s <- readFile f
     case parse s of
       Left err  -> error $ "Parse failed: " ++ err
       Right thy ->
         if "why3" `elem` es
           then putStrLn (render (Why3.ppTheory (lint "why3" (why3VarTheory (lint "parse" thy)))))
           else putStrLn (render (SMT.ppTheory (lint "parse" thy)))

