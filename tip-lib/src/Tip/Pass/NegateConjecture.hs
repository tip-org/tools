{-# LANGUAGE PatternGuards #-}
module Tip.Pass.NegateConjecture where

import Tip
import Tip.Fresh
import Control.Monad
import Data.Generics.Geniplate

-- | Negates the conjecture: changes assert-not into assert, and
--   introduce skolem types in case the goal is polymorphic.
negateConjecture :: Name a => Theory a -> Fresh (Theory a)
negateConjecture thy =
  foldM negateConjecture1
    thy { thy_form_decls = filter (not . isProve) (thy_form_decls thy) }
    (filter isProve (thy_form_decls thy))
  where
    isProve (Formula Prove _ form) = True
    isProve _ = False

    negateConjecture1 thy (Formula Prove tvs form) = do
      tvs' <- mapM (refreshNamed "sk_") tvs
      return thy {
        thy_form_decls = Formula Assert [] (neg (makeTyCons (zip tvs tvs') form)):thy_form_decls thy,
        thy_abs_type_decls = [ AbsType tv 0 | tv <- tvs' ] ++ thy_abs_type_decls thy }

    makeTyCons tvs =
      transformTypeInExpr $ \ty ->
        case ty of
          TyVar tv | Just tv' <- lookup tv tvs -> TyCon tv' []
          _ -> ty
