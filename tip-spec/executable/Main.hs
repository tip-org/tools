{-# LANGUAGE CPP #-}
#ifdef STACK
{-# LANGUAGE TemplateHaskell #-}
#endif
module Main where

import System.Environment

import Tip.QuickSpec
import Tip.Parser (parse)
#ifdef STACK
import Language.Haskell.TH.Syntax
import System.Process
#endif

import qualified Tip.Pretty.SMT as SMT

main :: IO ()
main = do
#ifdef STACK
  let pkgdb = $(qRunIO (readProcess "stack" ["exec", "--", "sh", "-c", "echo $GHC_PACKAGE_PATH"] "") >>= lift)

  setEnv "GHC_PACKAGE_PATH" (head (lines pkgdb))
#endif
  args <- getArgs
  case args of
     "-":es -> handle es =<< getContents
     f:es   -> handle es =<< readFile f
     es     -> handle es =<< getContents

handle :: [String] -> String -> IO ()
handle es s =
  case parse s of
    Left err  -> error $ "Parse failed: " ++ err
    Right thy ->
      do thy' <- exploreTheory thy
         print (SMT.ppTheory thy')

