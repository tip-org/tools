module Main where

import System.Environment

import Tip.Parser
import Tip.Pretty.SMT as SMT
import Tip.Pretty.Equations as Equations
import Tip.Pretty.TFF as TFF
import Tip.Pretty.Why3 as Why3
import Tip.Pretty.Isabelle as Isabelle
import Tip.Pretty.Haskell as HS
import Tip.Pretty.Hipster as Hipster
import Tip.Pretty.Hopster as Hopster
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
import Text.PrettyPrint hiding ((<>))

data OutputMode = Haskell HS.Mode | Why3 | SMTLIB Bool Bool | Isabelle Bool | Hipster | Hopster | TIP | TFF | Twee | Waldmeister | Equations | Vampire

parseOutputMode :: Parser OutputMode
parseOutputMode =
      flag' (Haskell HS.Plain)          (long "haskell"        <> help "Haskell output")
  <|> flag' (Haskell HS.Feat)           (long "haskell-feat"   <> help "Haskell output with Feat tests")
  <|> flag' (Haskell HS.QuickCheck)     (long "haskell-qc"     <> help "Haskell output with QuickCheck tests (Feat generators)")
  <|> flag' (Haskell (HS.LazySmallCheck False True))  (long "haskell-lazysc"        <> help "Haskell output with LazySmallCheck tests")
  <|> flag' (Haskell (HS.LazySmallCheck False False)) (long "haskell-lazysc-simple" <> help "Haskell output with LazySmallCheck tests, with parallel operators only in the property")
  <|> flag' (Haskell (HS.LazySmallCheck True  True))  (long "haskell-lazysc-depth"  <> help "Haskell output with LazySmallCheck tests up to some depth (given on command line)")
  <|> flag' (Haskell HS.Smten)                  (long "haskell-smten"        <> help "Haskell output with Smten (depth given on command line)")
  <|> flag' (Haskell (HS.QuickSpec (HS.QuickSpecParams {foreground_functions = Nothing, predicates = Nothing, max_test_size = 20, max_size = 7, max_depth = maxBound, use_observers = False, max_observer_size = 0, use_completion = False, exploration_timeout = Nothing, int_is_nat = False, only_recursive_functions = False})))      (long "haskell-spec"   <> help "Haskell output with QuickSpec signature (Feat generators)")
  <|> flag' Why3 (long "why" <> help "WhyML output")
  <|> flag' (SMTLIB False False) (long "smtlib" <> help "SMTLIB output")
  <|> flag' (SMTLIB False True) (long "smtlib-no-match" <> help "SMTLIB output (eliminate match)")
  <|> flag' (SMTLIB True True)  (long "smtlib-ax-fun" <> help "SMTLIB output (eliminate match and function declarations)")
  <|> flag' (Isabelle False) (long "isabelle" <> help "Isabelle output")
  <|> flag' (Isabelle True) (long "isabelle-explicit-forall" <> help "Isabelle output (with variables explicitly forall quantified)")
  <|> flag' Hopster (long "hopster" <> help "Hopster output")
  <|> flag' Hipster (long "hipster" <> help "Only conjectrures, in Isabelle format. For internal use in Hipster.")
  <|> flag' TFF (long "tff" <> help "TPTP TFF output")
  <|> flag' Twee (long "twee" <> help "TPTP TFF output (equational)")
  <|> flag' Waldmeister (long "waldmeister" <> help "Waldmeister output")
  <|> flag  TIP TIP (long "tip" <> help "TIP output (default)")
  <|> flag' Equations (long "equations" <> help "Pretty-print conjectures as equations")
  <|> flag' Vampire (long "vampire" <> help "Use assert-claim for conjectures in Vampire")
  
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
              SMTLIB ax_func_decls remove_match ->
                ( \t -> SMT.ppTheory SMT.smtConfig t
                , passes ++
                  [ Monomorphise False 1
                  , AxiomatizeLambdas
                  , SimplifyGently, CollapseEqual]
                  ++ concat [ [SimplifyGently, RemoveMatch] | remove_match ]
                  ++ [ SimplifyGently, Monomorphise False 1 ]
                  ++ [ AxiomatizeFuncdefs | ax_func_decls ]
                  ++ [ SimplifyGently ]
                , "smt2")
              TFF ->
                ( TFF.ppTheory
                , passes ++
                  [ Monomorphise False 1
                  , AxiomatizeLambdas
                  , SimplifyGently, CollapseEqual
                  , SimplifyGently, Monomorphise False 1, IfToBoolOp, CommuteMatch
                  , SimplifyGently, AxiomatizeFuncdefs2, RemoveMatch, SimplifyGently, LetLift
                  , SimplifyGently, AxiomatizeDatadecls
                  ]
                , "p")
              Twee ->
                ( TFF.ppTheory
                , passes ++
                  [ Monomorphise False 1
                  , AxiomatizeLambdas
                  , SimplifyGently, CollapseEqual
                  , SimplifyGently, Monomorphise False 1, IfToBoolOp, IntToNat, RemoveBuiltinBool, CommuteMatch
                  , SimplifyGently, LetLift, SimplifyGently, AxiomatizeFuncdefs2
                  , SimplifyGently, AxiomatizeDatadeclsUEQ
                  ]
                , "p")
              Waldmeister ->
                ( Waldmeister.ppTheory . freshPass uniqLocals
                , passes ++
                  [ Monomorphise False 1
                  , AxiomatizeLambdas, LetLift
                  , CollapseEqual
                  , Monomorphise False 1
                  , AxiomatizeFuncdefs2, AxiomatizeDatadeclsUEQ
                  , SkolemiseConjecture
                  ]
                , "w")
              Haskell m -> (HS.ppTheory m,     passes, "hs")
              Why3      -> (Why3.ppTheory,     passes ++ [CSEMatchWhy3], "mlw")
              Isabelle expl_forall -> (Isabelle.ppTheory expl_forall, passes, "thy")
              Hipster -> (Hipster.ppHipsterConjs, passes, "txt")
              Hopster -> (Hopster.ppHopsterConjs, passes, "txt")
              TIP       -> (SMT.ppTheory SMT.tipConfig, passes, "smt2")
              Equations -> (Equations.ppEquations, passes, "txt")
              Vampire ->
                ( \t -> SMT.ppTheory SMT.vampConfig t
                , passes ++
                  [ Monomorphise False 1
                  , AxiomatizeLambdas
                  , SimplifyGently, CollapseEqual]
                  ++ [ SimplifyGently, Monomorphise False 1 ]    
                  ++ [ SimplifyGently ]
                , "smt2")
      let thys = freshPass (runPasses pipeline) (lint "parse" thy)
      case multipath of
        Nothing ->
          case thys of
            [thy] -> print (pretty thy)
            []    -> error "No theory remaining"
            _     -> error "Multiple theories, specify an output path"
        Just d ->
          sequence_
            [ do putStrLn $ d ++ show n <.> ext
                 writeFile (d ++ show n <.> ext) (show (pretty thy) ++ "\n")
            | (n, thy) <- [(0 :: Int)..] `zip` thys
            ]
