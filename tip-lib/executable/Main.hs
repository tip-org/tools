module Main where

import System.Environment
import Text.PrettyPrint

import Tip.Parser
import Tip.Pretty.SMT as SMT
import Tip.Pretty.Why3 as Why3
import Tip.Pretty.Isabelle as Isabelle
import Tip.Pretty.Haskell as HS

import Tip.Passes
import Tip.Lint
import Tip.Fresh
import Tip.Core

import Control.Monad

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
    Right thy -> do
      let passes :: [StandardPass]
          (passes,other) = parsePasses es
      let pp f = fmap (show . f)
      let show_passes c = fmap (\ s -> c ++ show passes ++ "\n" ++ s)
      let pipeline
            | "cvc4" `elem` other =
                pp SMT.ppTheory .
                runPasses
                  [ LambdaLift, AxiomatizeLambdas
                  , CollapseEqual, RemoveAliases
                  , SimplifyGently, RemoveMatch
                  , SimplifyGently, NegateConjecture
                  , SimplifyGently
                  ]
            | "hs" `elem` other       = fmap show . HS.ppTheory <=< runPasses passes
            | "why3" `elem` other     = pp Why3.ppTheory . runPasses (passes ++ [CSEMatchWhy3])
            | "isabelle" `elem` other = pp Isabelle.ppTheory . runPasses passes
            | otherwise               = show_passes "; " . pp SMT.ppTheory .  runPasses passes
      putStrLn (freshPass pipeline (lint "parse" thy))
