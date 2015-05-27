module Tip.Pretty.Haskell where

import Tip.Haskell.Repr
import Tip.Haskell.Translate
import Tip.Haskell.Rename
import Tip.Core
import Tip.Pretty
import Tip.Fresh
import Text.PrettyPrint

ppTheory :: (Name a,PrettyVar a) => Theory a -> Fresh Doc
ppTheory = fmap (pp . renameDecls) . trTheory

