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
    thy { thy_asserts = filter (not . isProve) (thy_asserts thy) }
    (filter isProve (thy_asserts thy))
  where
    isProve (Formula Prove _ form) = True
    isProve _ = False

    negateConjecture1 thy (Formula Prove tvs form) = do
      tvs' <- mapM (refreshNamed "sk_") tvs
      return thy {
        thy_asserts = Formula Assert [] (neg (makeTyCons (zip tvs tvs') form)):thy_asserts thy,
        thy_sorts = [ Sort tv 0 | tv <- tvs' ] ++ thy_sorts thy }

    makeTyCons tvs =
      transformTypeInExpr $ \ty ->
        case ty of
          TyVar tv | Just tv' <- lookup tv tvs -> TyCon tv' []
          _ -> ty
