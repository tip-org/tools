module Tip.QuickSpec (module Tip.QuickSpec, RenameMap, module Tip.QuickSpec.Translate) where

import Tip.QuickSpec.Translate -- for reexport

import Tip.Pretty.Haskell
import Tip.Fresh (Name)
import Tip.Haskell.Translate
import Tip.Core (Theory)

import QuickSpec (Signature, Constant)

import Language.Haskell.Interpreter
import System.FilePath
import System.Directory
import System.IO.Temp

type ChoppedSignature = ([(Constant,[Int])],Signature)

theorySignature :: Name a => Theory a -> IO (ChoppedSignature,RenameMap a)
theorySignature thy =
  fmap (either (error . show) id) $
  withSystemTempDirectory "tip-spec" $
    \ dir ->
      do let a_file = dir </> "A" <.> "hs"
         let (thy_doc, rename_map) = ppTheoryWithRenamings thy
         writeFile a_file (show thy_doc)
         setCurrentDirectory dir
         runInterpreter $
           do loadModules ["A"]
              setImports ["A","QuickSpec.Signature","QuickSpec.Term","Prelude"]
              sig <- interpret "sig" (undefined :: ChoppedSignature)
              return (sig,rename_map)

