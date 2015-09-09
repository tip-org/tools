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

data MinOpt = MinEnabled | MinDisabled

data OutputMode = Haskell HS.Mode | Why3 | SMTLIB Bool | Isabelle | TIP | TFF MinOpt

parseOutputMode :: Parser OutputMode
parseOutputMode =
      flag' (Haskell HS.Plain)          (long "haskell"        <> help "Haskell output")
  <|> flag' (Haskell HS.Feat)           (long "haskell-feat"   <> help "Haskell output with Feat tests")
  <|> flag' (Haskell HS.QuickCheck)     (long "haskell-qc"     <> help "Haskell output with QuickCheck tests (Feat generators)")
  <|> flag' (Haskell HS.LazySmallCheck) (long "haskell-lazysc" <> help "Haskell output with LazySmallCheck tests")
  <|> flag' (Haskell HS.QuickSpec)      (long "haskell-spec"   <> help "Haskell output with QuickSpec signature (Feat generators)")
  <|> flag' Why3 (long "why" <> help "WhyML output")
  <|> flag' (SMTLIB False) (long "smtlib" <> help "SMTLIB output")
  <|> flag' (SMTLIB True)  (long "smtlib-ax-fun" <> help "SMTLIB output (axiomatise function declarations)")
  <|> flag' Isabelle (long "isabelle" <> help "Isabelle output")
  <|> flag' (TFF MinDisabled) (long "tff" <> help "TPTP TFF output")
  <|> flag' (TFF MinEnabled)  (long "tff-min" <> help "TPTP TFF output with Min")
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
              SMTLIB ax_func_decls ->
                ( SMT.ppTheory
                , passes ++
                  [ TypeSkolemConjecture, Monomorphise False
                  , LambdaLift, AxiomatizeLambdas
                  , SimplifyGently, CollapseEqual, RemoveAliases
                  , SimplifyGently, RemoveMatch
                  , SimplifyGently, Monomorphise False ]
                  ++ [ AxiomatizeFuncdefs | ax_func_decls ]
                  ++ [ SimplifyGently, NegateConjecture ]
                , "smt2")
              TFF min_mode ->
                ( TFF.ppTheory
                , passes ++
                  [ TypeSkolemConjecture, Monomorphise False
                  , LambdaLift, AxiomatizeLambdas
                  , SimplifyGently, CollapseEqual, RemoveAliases
                  , SimplifyGently, Monomorphise False, IfToBoolOp, CommuteMatch
                  , SimplifyGently, LetLift, SimplifyGently
                  ] ++
                  case min_mode of
                    MinEnabled  -> [Min]
                    MinDisabled -> [AxiomatizeFuncdefs2, SimplifyGently, AxiomatizeDatadecls]
                , "p")
              Haskell m -> (HS.ppTheory m,     passes, "hs")
              Why3      -> (Why3.ppTheory,     passes ++ [CSEMatchWhy3], "mlw")
              Isabelle  -> (Isabelle.ppTheory, passes, "thy")
              TIP       -> (SMT.ppTheory,      passes, "smt2")
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

