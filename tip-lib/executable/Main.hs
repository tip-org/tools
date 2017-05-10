module Main where

import System.Environment

import Tip.Parser
import Tip.Pretty.SMT as SMT
import Tip.Pretty.TFF as TFF
import Tip.Pretty.Why3 as Why3
import Tip.Pretty.Isabelle as Isabelle
import Tip.Pretty.Haskell as HS
import Tip.Pretty.Hipster as Hipster
import Tip.Haskell.Translate as HS
import Tip.Pretty.Waldmeister as Waldmeister
import Tip.Pretty
import Tip.CallGraph

import Tip.Passes
import Tip.Lint
import Tip.Fresh
import Tip.Core

import System.FilePath
import Options.Applicative
import Control.Monad
import Data.Monoid ((<>))

data OutputMode = Haskell HS.Mode | Why3 | SMTLIB Bool | Isabelle Bool | Hipster | TIP | TFF | Waldmeister

parseOutputMode :: Parser OutputMode
parseOutputMode =
      flag' (Haskell HS.Plain)          (long "haskell"        <> help "Haskell output")
  <|> flag' (Haskell HS.Feat)           (long "haskell-feat"   <> help "Haskell output with Feat tests")
  <|> flag' (Haskell HS.QuickCheck)     (long "haskell-qc"     <> help "Haskell output with QuickCheck tests (Feat generators)")
  <|> flag' (Haskell (HS.LazySmallCheck False True))  (long "haskell-lazysc"        <> help "Haskell output with LazySmallCheck tests")
  <|> flag' (Haskell (HS.LazySmallCheck False False)) (long "haskell-lazysc-simple" <> help "Haskell output with LazySmallCheck tests, with parallel operators only in the property")
  <|> flag' (Haskell (HS.LazySmallCheck True  True))  (long "haskell-lazysc-depth"  <> help "Haskell output with LazySmallCheck tests up to some depth (given on command line)")
  <|> flag' (Haskell HS.Smten)                  (long "haskell-smten"        <> help "Haskell output with Smten (depth given on command line)")
  <|> flag' (Haskell (HS.QuickSpec (HS.QuickSpecParams [])))      (long "haskell-spec"   <> help "Haskell output with QuickSpec signature (Feat generators)")
  <|> flag' Why3 (long "why" <> help "WhyML output")
  <|> flag' (SMTLIB False) (long "smtlib" <> help "SMTLIB output")
  <|> flag' (SMTLIB True)  (long "smtlib-ax-fun" <> help "SMTLIB output (axiomatise function declarations)")
  <|> flag' (Isabelle False) (long "isabelle" <> help "Isabelle output")
  <|> flag' (Isabelle True) (long "isabelle-explicit-forall" <> help "Isabelle output (with variables explicitly forall quantified)")
  <|> flag' Hipster (long "hipster" <> help "Only conjectrures, in Isabelle format. For internal use in Hipster.")
  <|> flag' TFF (long "tff" <> help "TPTP TFF output")
  <|> flag' Waldmeister (long "waldmeister" <> help "Waldmeister output")
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
                ( SMT.ppTheory SMT.smtKeywords
                , passes ++
                  [ TypeSkolemConjecture, Monomorphise False
                  , LambdaLift, AxiomatizeLambdas
                  , SimplifyGently, CollapseEqual, RemoveAliases
                  , SimplifyGently, RemoveMatch
                  , SimplifyGently, Monomorphise False ]
                  ++ [ AxiomatizeFuncdefs | ax_func_decls ]
                  ++ [ SimplifyGently, NegateConjecture, DropAttributes ]
                , "smt2")
              TFF ->
                ( TFF.ppTheory
                , passes ++
                  [ TypeSkolemConjecture, Monomorphise False
                  , LambdaLift, AxiomatizeLambdas
                  , SimplifyGently, CollapseEqual, RemoveAliases
                  , SimplifyGently, Monomorphise False, IfToBoolOp, CommuteMatch
                  , SimplifyGently, LetLift, SimplifyGently, AxiomatizeFuncdefs2
                  , SimplifyGently, AxiomatizeDatadecls
                  ]
                , "p")
              Waldmeister ->
                ( Waldmeister.ppTheory . freshPass uniqLocals
                , passes ++
                  [ TypeSkolemConjecture, Monomorphise False
                  , LambdaLift, AxiomatizeLambdas, LetLift
                  , CollapseEqual, RemoveAliases
                  , Monomorphise False
                  , AxiomatizeFuncdefs2, AxiomatizeDatadeclsUEQ
                  , SkolemiseConjecture
                  ]
                , "w")
              Haskell m -> (HS.ppTheory m,     passes, "hs")
              Why3      -> (Why3.ppTheory,     passes ++ [CSEMatchWhy3], "mlw")
              Isabelle expl_forall -> (Isabelle.ppTheory expl_forall, passes, "thy")
              Hipster -> (Hipster.ppHipsterConjs, passes, "txt")
              TIP       -> (SMT.ppTheory [],      passes, "smt2")
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
