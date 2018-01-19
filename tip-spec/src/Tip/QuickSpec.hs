module Tip.QuickSpec (module Tip.QuickSpec, RenameMap, module Tip.QuickSpec.Translate) where

import Tip.QuickSpec.Translate -- for reexport

import Tip.Pretty.Haskell
import Tip.Fresh (Name)
import Tip.Haskell.Translate
import Tip.Core (Theory)

import qualified QuickSpec.Signature as QS
import qualified QuickSpec.Pruning as QS
import qualified QuickSpec.Pruning.Completion as QS
import QuickSpec (Signature)
import QuickSpec.Term(Constant)
import QuickSpec.Eval(choppyQuickSpec, shouldPrint)

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

type ChoppedSignature = ([(Constant,[Int])],Signature)

theorySignature :: Name a => QuickSpecParams -> Theory a -> IO (ChoppedSignature,RenameMap a)
theorySignature params thy =
  withSystemTempDirectory "tip-spec" $
    \ dir ->
      do let a_file = dir </> "A" <.> "hs"
         let (thy_doc, rename_map) = ppTheoryWithRenamings "A" (QuickSpec params) thy
         writeFile a_file (show thy_doc)
         setCurrentDirectory dir
         r <- runInterpreter $
           do unsafeSetGhcOption "-hide-package QuickCheck"
              unsafeSetGhcOption "-package QuickCheck-2.8.2"
              loadModules ["A"]
              setImports ["A","QuickSpec.Signature","QuickSpec.Term","Prelude"]
              sig <- interpret "sig" (undefined :: ChoppedSignature)
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
  do ((chops,sig),rm) <- theorySignature params thy
     let disableCompletion sig = sig { QS.theory = Just ((QS.emptyPruner sig) { QS.addCriticalPairs = False }) }
     sig' <- toStderr $ choppyQuickSpec chops (disableCompletion sig)
     let bm  = backMap thy rm
     let fms = mapM (trProperty bm) (filter shouldPrint (nub (QS.background sig'))) `freshFrom` thy
     return thy { thy_asserts = thy_asserts thy ++ fms }

toStderr :: IO a -> IO a
toStderr mx = do
  oldStdout <- hDuplicate stdout
  hDuplicateTo stderr stdout
  x <- mx
  hDuplicateTo oldStdout stdout
  hClose oldStdout
  return x

