module Main where

import System.Environment
import Text.PrettyPrint
import Tip.Parser
import Tip.Pretty.SMT as SMT
import Tip.Pretty.Why3 as Why3
import Tip.Lint
import Tip.Fresh
import Tip.Simplify
import Tip.Decase
import Tip.Lift
import Tip.EqualFunctions
import Tip.Deprove
import Tip
import Control.Monad

main :: IO ()
main =
  do f:es <- getArgs
     s <- readFile f
     case parse s of
       Left err  -> error $ "Parse failed: " ++ err
       Right thy ->
         let pipeline =
               case () of
                 () | "why3" `elem` es -> return . Why3.ppTheory
                 () | "cvc4" `elem` es ->
                   lambdaLift >=> return . lint "lambdaLift" >=>
                   axiomatizeLambdas >=> return . lint "axiomatizeLambdas" >=>
                   return . lint "collapseEqual" . collapseEqual >=>
                   return . lint "removeAliases" . removeAliases >=>
                   simplifyExpr gently >=> return . lint "simplify1" >=>
                   decase >=> return . lint "decase" >=>
                   simplifyExpr gently >=> return . lint "simplify2" >=>
                   deprove >=> return . lint "deprove" >=>
                   simplifyExpr gently >=> return . lint "simplify3" >=>
                   return . SMT.ppTheory
                 _ ->
                   return . SMT.ppTheory in
         print (freshPass pipeline (lint "parse" thy))
