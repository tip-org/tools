module Tip.Pretty.Haskell where

import Tip.Haskell.Repr
import Tip.Haskell.Translate
import Tip.Core
import Tip.Pretty
import Text.PrettyPrint

ppTheory :: (HsVar a,HaskellVar a) => Theory a -> Doc
ppTheory = pp . trTheory

