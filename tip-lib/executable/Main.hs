module Main where

import System.Environment

import Tip.Parser
import Tip.Pretty.SMT as SMT
import Tip.Pretty.TFF as TFF
import Tip.Pretty.Why3 as Why3
import Tip.Pretty.Isabelle as Isabelle
import Tip.Pretty.Haskell as HS
import Tip.Pretty
import Tip.CallGraph

import Tip.Passes
import Tip.Lint
import Tip.Fresh
import Tip.Core

import System.FilePath
import Options.Applicative
import Control.Monad

data OutputMode = Haskell | Why3 | CVC4 | Isabelle | TIP | TFF

parseOutputMode :: Parser OutputMode
parseOutputMode =
      flag' Haskell (long "haskell" <> help "Haskell output")
  <|> flag' Why3 (long "why" <> help "WhyML output")
  <|> flag' CVC4 (long "smtlib" <> help "SMTLIB output (CVC4-compatible)")
  <|> flag' Isabelle (long "isabelle" <> help "Isabelle output")
  <|> flag' TFF (long "tff" <> help "TPTP TFF output")
  <|> flag  TIP TIP (long "tip" <> help "TIP output (default)")

optionParser :: Parser ([StandardPass], Maybe String, OutputMode, Maybe FilePath)
optionParser =
  (,,,) <$> parsePasses <*> parseFile <*> parseOutputMode <*> parseMultiPath
  where
    parseFile =
      fmap Just (strArgument (metavar "FILENAME")) <|> pure Nothing

    parseMultiPath =
      fmap Just (strArgument (metavar "DIRECTORY")) <|> pure Nothing

main :: IO ()
main = do
  (passes, files, mode, multipath) <-
    execParser $
      info (helper <*> optionParser)
        (fullDesc <>
         progDesc "Transform a TIP problem" <>
         header "tip - a tool for processing TIP problems")
  case files of
    Nothing  -> handle passes mode multipath =<< getContents
    Just "-" -> handle passes mode multipath =<< getContents
    Just f   -> handle passes mode multipath =<< readFile f

handle :: [StandardPass] -> OutputMode -> Maybe FilePath -> String -> IO ()
handle passes mode multipath s =
  case parse s of
    Left err  -> error $ "Parse failed: " ++ err
    Right thy -> do
      let fmap_pp f = fmap (show . map f)
      let show_passes c = fmap (\ s -> c ++ show passes ++ "\n" ++ s)
      let (pretty,pipeline,ext) =
            case mode of
              CVC4 ->
                ( SMT.ppTheory
                , passes ++
                  [ TypeSkolemConjecture, Monomorphise
                  , LambdaLift, AxiomatizeLambdas
                  , SimplifyGently, CollapseEqual, RemoveAliases
                  , SimplifyGently, RemoveMatch
                  , SimplifyGently, Monomorphise, AxiomatizeFuncdefs
                  , SimplifyGently, NegateConjecture
                  ]
                , "smt2")
              TFF ->
                ( TFF.ppTheory
                , passes ++
                  [ TypeSkolemConjecture, Monomorphise
                  , LambdaLift, AxiomatizeLambdas
                  , SimplifyGently, CollapseEqual, RemoveAliases
                  , SimplifyGently, Monomorphise, IfToBoolOp, CommuteMatch
                  , SimplifyGently, LetLift, SimplifyGently, AxiomatizeFuncdefs2
                  , SimplifyGently, AxiomatizeDatadecls
                  ]
                , "p")
              Haskell  -> (HS.ppTheory,       passes, "hs")
              Why3     -> (Why3.ppTheory,     passes ++ [CSEMatchWhy3], "mlw")
              Isabelle -> (Isabelle.ppTheory, passes, "thy")
              TIP      -> (SMT.ppTheory,      passes, "smt2")
      let thys = freshPass (runPasses pipeline) (lint "parse" thy)
      case multipath of
        Nothing ->
          case thys of
            [thy] -> print (pretty thy)
            []    -> error "No theory remaining"
            _     -> error "Multiple theories, specify an output path"
        Just d ->
          sequence_
            [ do putStrLn $ d </> show n <.> ext
                 writeFile (d </> show n <.> ext) (show (pretty thy) ++ "\n")
            | (n, thy) <- [(0 :: Int)..] `zip` thys
            ]

