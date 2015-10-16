module Tip.QuickSpec (module Tip.QuickSpec, RenameMap, module Tip.QuickSpec.Translate) where

import Tip.QuickSpec.Translate -- for reexport

import Tip.Pretty.Haskell
import Tip.Fresh (Name)
import Tip.Haskell.Translate
import Tip.Core (Theory)

import qualified QuickSpec.Signature as QS
import QuickSpec (Signature, Constant, choppyQuickSpec)

import Language.Haskell.Interpreter
import System.FilePath
import System.Directory
import System.IO.Temp

import Tip.Core hiding (Signature)
import Tip.Fresh
import Tip.Utils
import Data.List
import GHC.IO.Handle
import System.IO

type ChoppedSignature = ([(Constant,[Int])],Signature)

theorySignature :: Name a => Theory a -> IO (ChoppedSignature,RenameMap a)
theorySignature thy =
  withSystemTempDirectory "tip-spec" $
    \ dir ->
      do let a_file = dir </> "A" <.> "hs"
         let (thy_doc, rename_map) = ppTheoryWithRenamings "A" QuickSpec thy
         writeFile a_file (show thy_doc)
         setCurrentDirectory dir
         r <- runInterpreter $
           do loadModules ["A"]
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

exploreTheory :: Name a => Theory a -> IO (Theory a)
exploreTheory thy =
  do ((chops,sig),rm) <- theorySignature thy
     sig' <- toStderr $ choppyQuickSpec chops sig
     let bm  = backMap thy rm
     let fms = mapM (trProperty bm) (nub (QS.background sig')) `freshFrom` thy
     return thy { thy_asserts = thy_asserts thy ++ fms }

toStderr :: IO a -> IO a
toStderr mx = do
  oldStdout <- hDuplicate stdout
  hDuplicateTo stderr stdout
  x <- mx
  hDuplicateTo oldStdout stdout
  hClose oldStdout
  return x

