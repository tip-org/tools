module Main where

import System.Environment

import Tip.Parser
import Tip.Pretty.SMT as SMT
import Tip.Pretty.Why3 as Why3
import Tip.Pretty.Isabelle as Isabelle
import Tip.Pretty.Haskell as HS
import Tip.Pretty
import Tip.CallGraph

import Tip.Passes
import Tip.Lint
import Tip.Fresh
import Tip.Core
import Options.Applicative

import Control.Monad

data OutputMode = Haskell | Why3 | CVC4 | Isabelle | TIP

parseOutputMode :: Parser OutputMode
parseOutputMode =
      flag' Haskell (long "haskell" <> help "Haskell output")
  <|> flag' Why3 (long "why" <> help "WhyML output")
  <|> flag' CVC4 (long "smtlib" <> help "SMTLIB output (CVC4-compatible)")
  <|> flag' Isabelle (long "isabelle" <> help "Isabelle output")
  <|> flag  TIP TIP (long "tip" <> help "TIP output (default)")

optionParser :: Parser ([StandardPass], Maybe String, OutputMode)
optionParser =
  (,,) <$> parsePasses <*> parseFile <*> parseOutputMode
  where
    parseFile =
      fmap Just (strArgument (metavar "FILENAME")) <|> pure Nothing

main :: IO ()
main = do
  (passes, files, mode) <-
    execParser $
      info (helper <*> optionParser)
        (fullDesc <>
         progDesc "Transform a TIP problem" <>
         header "tip - a tool for processing TIP problems")
  case files of
    Nothing ->
      handle passes mode =<< getContents
    Just f ->
      handle passes mode =<< readFile f

handle :: [StandardPass] -> OutputMode -> String -> IO ()
handle passes mode s =
  case parse s of
    Left err  -> error $ "Parse failed: " ++ err
    Right thy -> do
      let fmap_pp f = fmap (show . f)
      let show_passes c = fmap (\ s -> c ++ show passes ++ "\n" ++ s)
      let pipeline =
            case mode of
              CVC4 ->
                fmap_pp SMT.ppTheory . runPasses
                  (passes ++
                  [ LambdaLift, AxiomatizeLambdas
                  , CollapseEqual, RemoveAliases
                  , SimplifyGently, RemoveMatch
                  , SimplifyGently, NegateConjecture, AxiomatizeFuncdefs
                  , SimplifyGently
                  ])
              Haskell ->
                fmap_pp HS.ppTheory . runPasses passes
              Why3 ->
                fmap_pp Why3.ppTheory . runPasses (passes ++ [CSEMatchWhy3])
              Isabelle ->
                fmap_pp Isabelle.ppTheory . runPasses passes
              TIP ->
                show_passes "; " . fmap_pp SMT.ppTheory . runPasses passes
      putStrLn (freshPass pipeline (lint "parse" thy))
