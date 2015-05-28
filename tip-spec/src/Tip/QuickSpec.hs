module Tip.QuickSpec where

import Tip.Pretty.Haskell
import Tip.Fresh (Name)
import Tip.Haskell.Translate
import Tip.Core (Theory)

import QuickSpec.Signature (Signature)
import Language.Haskell.Interpreter
import System.FilePath
import System.Directory
import System.IO.Temp

import Data.Map (Map)

theorySignature :: Name a => Theory a -> IO (Signature,Map (HsId a) (HsId String))
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
              setImports ["A","QuickSpec.Signature"]
              sig <- interpret "sig" (undefined :: QuickSpec.Signature.Signature)
              return (sig,rename_map)

