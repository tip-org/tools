module Tip.Pretty.Haskell where

import Tip.Utils.Haskell
import Tip.Utils.ToHaskell
import Tip.Core
import Tip.Pretty
import Text.PrettyPrint

ppTheory :: (HsVar a,HaskellVar a) => Theory a -> Doc
ppTheory = pp . trTheory

