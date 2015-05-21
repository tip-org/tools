module Main where

import System.Environment
import Text.PrettyPrint

import Tip.Parser
import Tip.Pretty.SMT as SMT
import Tip.Pretty.Why3 as Why3
import Tip.Pretty.Isabelle as Isabelle

import Tip.Passes
import Tip.Lint
import Tip.Fresh
import Tip.Core

import Control.Monad

main :: IO ()
main =
  do f:es <- getArgs
     s <- readFile f
     case parse s of
       Left err  -> error $ "Parse failed: " ++ err
       Right thy -> do
         let passes :: [StandardPass]
             (passes,extra) = parsePasses es
         let pipeline
               | "cvc4" `elem` es =
                   fmap SMT.ppTheory .
                   runPasses
                     [ LambdaLift, AxiomatizeLambdas
                     , CollapseEqual, RemoveAliases
                     , SimplifyGently, RemoveMatch
                     , SimplifyGently, NegateConjecture
                     , SimplifyGently
                     ]
               | "why3" `elem` es     = fmap Why3.ppTheory . runPasses passes
               | "isabelle" `elem` es = fmap Isabelle.ppTheory . runPasses passes
               | otherwise            = fmap SMT.ppTheory .  runPasses passes
         when (not (null passes)) (putStrLn $ "; " ++ show passes)
         print (freshPass pipeline (lint "parse" thy))
