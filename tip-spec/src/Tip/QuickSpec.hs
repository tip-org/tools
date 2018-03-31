module Tip.QuickSpec (module Tip.QuickSpec, RenameMap, module Tip.QuickSpec.Translate) where

import Tip.QuickSpec.Translate -- for reexport

import Tip.Pretty.Haskell
import Tip.Fresh (Name)
import Tip.Haskell.Translate hiding (quickSpec)
import Tip.Core (Theory)

import QuickSpec

import Language.Haskell.Interpreter
import Language.Haskell.Interpreter.Unsafe
import System.FilePath
import System.Directory
import System.IO.Temp

import Tip.Core hiding (Signature)
import Tip.Fresh
import Data.List
import GHC.IO.Handle
import System.IO

theorySignature :: Name a => QuickSpecParams -> Theory a -> IO ([Sig], RenameMap a)
theorySignature params thy =
  withSystemTempDirectory "tip-spec" $
    \ dir ->
      do let a_file = dir </> "A" <.> "hs"
         let (thy_doc, rename_map) = ppTheoryWithRenamings "A" (QuickSpec params) thy
         writeFile a_file (show thy_doc)
         print thy_doc
         setCurrentDirectory dir
         r <- runInterpreter $
           do unsafeSetGhcOption "-hide-package QuickCheck"
              unsafeSetGhcOption "-package QuickCheck-2.10.1" --FIXME: is this the right QC version?
              loadModules ["A"]
              setImports ["A","QuickSpec","QuickSpec.Term","Prelude"]
              sig <- interpret "sig" (undefined :: [Sig])
              return (sig,rename_map)
         case r of
           Left (WontCompile errs) ->
             do mapM_ (putStrLn . errMsg) errs
                putStrLn (show thy_doc)
                error "theorySignature"
           Left err ->
             do print err
                error "theorySignature"
           Right sig -> return sig

exploreTheory :: Name a => QuickSpecParams -> Theory a -> IO (Theory a)
exploreTheory params thy =
  do (sig,rm) <- theorySignature params thy
     sig' <- toStderr (quickSpec $ [withPruningDepth 0] ++ sig)
     let bm  = backMap thy rm
     --let fms = mapM (trProperty bm) (filter shouldPrint (nub (QS.background sig'))) `freshFrom` thy
     --return thy { thy_asserts = thy_asserts thy ++ fms }
     return thy

toStderr :: IO a -> IO a
toStderr mx = do
  oldStdout <- hDuplicate stdout
  hDuplicateTo stderr stdout
  x <- mx
  hDuplicateTo oldStdout stdout
  hClose oldStdout
  return x

