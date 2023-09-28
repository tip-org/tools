module Tip.Pass.DropAttributes where

import Tip.Core

filterAttributes :: (String -> Bool) -> Theory a -> Theory a
filterAttributes p thy =
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
    clear x = putAttrs [attr | attr <- getAttrs x, p (fst attr)] x

dropAttributes :: Theory a -> Theory a
dropAttributes thy = filterAttributes (const False) thy

dropAttribute :: String -> Theory a -> Theory a
dropAttribute name thy = filterAttributes (/= name) thy
