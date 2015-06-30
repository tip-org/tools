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

import System.FilePath
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
      let (pretty,pipeline) =
            case mode of
              CVC4 ->
                ( SMT.ppTheory
                , passes ++
                  [ TypeSkolemConjecture, Monomorphise
                  , LambdaLift, AxiomatizeLambdas
                  , CollapseEqual, RemoveAliases
                  , SimplifyGently, RemoveMatch
                  , SimplifyGently, Monomorphise, AxiomatizeFuncdefs
                  , SimplifyGently, NegateConjecture
                  ]
                )
              Haskell  -> (HS.ppTheory,       passes)
              Why3     -> (Why3.ppTheory,     passes ++ [CSEMatchWhy3])
              Isabelle -> (Isabelle.ppTheory, passes)
              TIP      -> (SMT.ppTheory,      passes)
      case freshPass (runPasses pipeline) (lint "parse" thy) of
        [thy] -> print (pretty thy)
        []    -> error "No theory remaining"
        thys  ->
          case multipath of
            Nothing -> error "Multiple theories, specify an output path"
            Just d ->
              do putStrLn $ "Putting theories in " ++ d
                 sequence_
                   [ do putStrLn $ "Writing " ++ (d </> show n)
                        writeFile (d </> show n) (show (pretty thy))
                   | (n, thy) <- [(0 :: Int)..] `zip` thys
                   ]

