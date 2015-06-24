{-# LANGUAGE PatternGuards #-}
module Tip.Pass.NegateConjecture where

import Tip.Core
import Tip.Fresh
import Control.Monad
import Data.Generics.Geniplate

-- | Negates the conjecture: changes assert-not into assert, and
--   introduce skolem types in case the goal is polymorphic.
--   (runs 'typeSkolemConjecture')
negateConjecture :: Name a => Theory a -> Fresh (Theory a)
negateConjecture = fmap (declsPass (map neg1)) . typeSkolemConjecture
  where
  neg1 (AssertDecl (Formula Prove [] form))
      = AssertDecl (Formula Assert [] (gentleNeg form))
  neg1 d0 = d0

-- | Introduce skolem types in case the goal is polymorphic.
typeSkolemConjecture :: Name a => Theory a -> Fresh (Theory a)
typeSkolemConjecture thy =
  foldM ty_skolem1
    thy { thy_asserts = filter (not . isProve) (thy_asserts thy) }
    (filter isProve (thy_asserts thy))
  where
  isProve (Formula Prove _ form) = True
  isProve _ = False

  ty_skolem1 thy (Formula Prove tvs form) = do
    tvs' <- mapM (refreshNamed "sk_") tvs
    return thy {
      thy_asserts = Formula Prove [] (makeTyCons (zip tvs tvs') form):thy_asserts thy,
      thy_sorts = [ Sort tv [] | tv <- tvs' ] ++ thy_sorts thy }

  makeTyCons tvs =
    transformTypeInExpr $ \ty ->
      case ty of
        TyVar tv | Just tv' <- lookup tv tvs -> TyCon tv' []
        _ -> ty
