module Tip.QuickSpec (module Tip.QuickSpec, RenameMap, module Tip.QuickSpec.Translate) where

import Tip.QuickSpec.Translate -- for reexport

import Tip.Pretty.Haskell
import Tip.Fresh (Name)
import Tip.Haskell.Translate hiding (quickSpec)
import Tip.Core (Theory)

import QuickSpec.Internal

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
import System.Timeout
import Data.Maybe

theorySignature :: Name a => QuickSpecParams -> Theory a -> IO ([Sig], RenameMap a)
theorySignature params thy =
  withSystemTempDirectory "tip-spec" $
    \ dir ->
      do let a_file = dir </> "A" <.> "hs"
         let (thy_doc, rename_map) = ppTheoryWithRenamings "A" (QuickSpec params) thy
         writeFile a_file ("{-# OPTIONS_GHC -fobject-code -O #-}\n" ++ show thy_doc)
         --print thy_doc
         setCurrentDirectory dir
         r <- runInterpreter $
           do loadModules ["A"]
              setImports ["A","QuickSpec","Prelude"]
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
     let
       addTimeout action =
         case exploration_timeout params of
           Nothing -> action
           Just t -> fromMaybe [] <$> timeout (truncate (t * 1000000)) action

     sig' <- toStderr (addTimeout (quickSpecResult sig))
     let bm  = backMap thy rm
     let fms = mapM (trProperty bm) sig' `freshFrom` thy
     return thy { thy_asserts = thy_asserts thy ++ fms }

toStderr :: IO a -> IO a
toStderr mx = do
  oldStdout <- hDuplicate stdout
  hDuplicateTo stderr stdout
  x <- mx
  hDuplicateTo oldStdout stdout
  hClose oldStdout
  return x
