-- Split up formulas into smaller parts.
-- 1. forall x1..xn. (t & u) ===> (forall x1..xn. t) & (forall x1..xn). u
-- 2. forall x1..xn. (t = u) ===> (forall x1..xn. t => u) & (forall x1..xn. u => t)
--    if t, u have boolean type.
module Tip.Pass.SplitFormulas where

import Tip.Types
import Tip.Core

splitFormulas :: Ord a => Theory a -> Theory a
splitFormulas thy =
  thy { thy_asserts = concatMap splitForm (thy_asserts thy) }
  where
    splitForm form =
      [form{fm_body = body} | body <- split (fm_body form)]
    split (Quant info Forall xs body) =
      map (Quant info Forall xs) (split body)
    split (Builtin And :@: ts) =
      concatMap split ts
    split (Builtin Equal :@: ts@(t:_))
      | exprType t == BuiltinType Boolean =
        [ Builtin Implies :@: [t, u] | t <- ts, u <- ts, t /= u]
    split t = [t]
