module Main where

import System.Environment
import Text.PrettyPrint

import Tip.Parser
import Tip.Pretty.SMT as SMT
import Tip.Pretty.Why3 as Why3

import Tip.Passes
import Tip.Lint
import Tip.Fresh
import Tip

import Control.Monad

main :: IO ()
main =
  do f:es <- getArgs
     s <- readFile f
     case parse s of
       Left err  -> error $ "Parse failed: " ++ err
       Right thy -> do
         let pipeline =
               case () of
                 () | "why3" `elem` es -> return . Why3.ppTheory
                 () | "cvc4" `elem` es ->
                   lambdaLift >=> lintM "lambdaLift" >=>
                   axiomatizeLambdas >=> lintM "axiomatizeLambdas" >=>
                   lintM "collapseEqual" . collapseEqual >=>
                   lintM "removeAliases" . removeAliases >=>
                   simplifyTheory gently >=> lintM "simplify1" >=>
                   removeMatch >=> lintM "removeMatch" >=>
                   simplifyTheory gently >=> lintM "simplify2" >=>
                   negateConjecture >=> lintM "negateConjecture" >=>
                   simplifyTheory gently >=> lintM "simplify3" >=>
                   return . SMT.ppTheory
                 _ ->
                   return . SMT.ppTheory
         print (freshPass pipeline (lint "parse" thy))
