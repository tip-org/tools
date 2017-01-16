module Tip.Pass.DropAttributes where

import Tip.Core

dropAttributes :: Theory a -> Theory a
dropAttributes thy =
  thy {
    thy_datatypes =
      [ clear dt { data_cons = map clear (data_cons dt) }
      | dt <- thy_datatypes thy ],
    thy_sorts = map clear (thy_sorts thy),
    thy_sigs = map clear (thy_sigs thy),
    thy_funcs = map clear (thy_funcs thy),
    thy_asserts = map clear (thy_asserts thy) }
  where
    clear :: HasAttr a => a -> a
    clear = putAttrs []
