module Main where

import System.Environment

import Tip.QuickSpec
import Tip.Parser (parse)

import qualified Tip.Pretty.SMT as SMT

import QuickSpec (choppyQuickSpec)

import qualified QuickSpec.Signature as QS

import Tip.Core
import Tip.Fresh
import Tip.Utils

main :: IO ()
main =
  do args <- getArgs
     case args of
        "-":es -> handle es =<< getContents
        f:es   -> handle es =<< readFile f
        es     -> handle es =<< getContents

handle :: [String] -> String -> IO ()
handle es s =
  case parse s of
    Left err  -> error $ "Parse failed: " ++ err
    Right thy ->
      do ((chops,sig),rm) <- theorySignature thy
         sig' <- choppyQuickSpec chops sig
         let bm  = backMap thy rm
         let fms = mapM (trProperty bm) (usort (QS.background sig')) `freshFrom` thy
         print (SMT.ppTheory (thy { thy_asserts = thy_asserts thy ++ fms }))

