{-# LANGUAGE CPP, TemplateHaskell #-}
module Main where

import Tip.GHC
import Tip.GHC.Params
import Tip.Fresh
import Tip.Passes
import Tip.Pretty.SMT as SMT

import Options.Applicative
import Data.Monoid
#ifdef STACK
import Language.Haskell.TH.Syntax(qRunIO, lift)
import System.Process
import System.Environment
#endif

main :: IO ()
main = do
#ifdef STACK
    let pkgdb = $(qRunIO (readProcess "stack" ["exec", "--", "sh", "-c", "echo $GHC_PACKAGE_PATH"] "") >>= lift)

    setEnv "GHC_PACKAGE_PATH" (head (lines pkgdb))
#endif
    (file,params) <-
      execParser $
        info (helper <*>
                ((,) <$> strArgument (metavar "FILENAME" <> help "Haskell file to process")
                     <*> parseParams))
          (fullDesc <>
           progDesc "Translate Haskell to TIP" <>
           header "tip-ghc - translate Haskell to TIP")
    thy <- readHaskellFile params file
    let pipeline =
          freshPass $
            runPasses
              [ UncurryTheory
              , SimplifyGently
              , CommuteMatch
              , SimplifyGently
              , RemoveAliases
              , CollapseEqual
              ]
    case pipeline thy of
      [thy] -> print (SMT.ppTheory SMT.tipConfig thy)
      _     -> error "tip-ghc: not one theory!"
