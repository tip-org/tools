{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}
module Tip.Pass.Conjecture where

#include "errors.h"
import Tip.Core
import Tip.Fresh
import Control.Monad
import Control.Monad.Writer
import Data.Generics.Geniplate

-- | Splits a theory with many goals into many theories each with one goal
splitConjecture :: Theory a -> [Theory a]
splitConjecture thy =
  [ thy { thy_asserts = goal : assums } | goal <- goals ]
  where
  (goals,assums) = theoryGoals thy

-- | Splits, type skolems and skolemises conjectures!
skolemiseConjecture :: Name a => Theory a -> Fresh [Theory a]
skolemiseConjecture = mapM (skolemiseConjecture' <=< typeSkolemConjecture) . splitConjecture

-- | Skolemises a conjecture, assuming that there is just one goal and that it has no type variables.
skolemiseConjecture' :: Name a => Theory a -> Fresh (Theory a)
skolemiseConjecture' thy =
  case goals of
    [Formula Prove name i tvs body] ->
      case tvs of
        [] -> do let (body',(sks,pre)) = runWriter (skolemise body)

                 sks' <- sequence
                   [ do v' <- refresh v
                        return (Signature v' (PolyType [] [] t))
                   | Local v t <- sks
                   ]

                 let su = substMany (sks `zip` map (\ sk -> applySignature sk [] []) sks')

                 body'' <- su body'

                 pre'' <- mapM su pre

                 return thy {
                       thy_sigs    = sks' ++ thy_sigs thy,
                       thy_asserts = Formula Prove Nothing i [] body'' : map (formula Assert Nothing []) pre'' ++ assums
                     }
        _ -> ERROR("Cannot skolemise conjecture with type variables")
    _ -> ERROR("Need one conjecture to skolemise conjecture")
  where
  (goals,assums) = theoryGoals thy

  formula r n tvs (Quant (QuantIH i) q vs e) = Formula r n (IH i) tvs (mkQuant q vs e)
  formula r n tvs e = Formula r n Unknown tvs e

skolemise :: Expr a -> Writer ([Local a],[Expr a]) (Expr a)
skolemise = go True
  where
  go i e0 =
    case e0 of
      Quant qi Forall lcls e  -> tell (lcls,[]) >> go True e
      Builtin Not :@: [e] | i -> go False (neg e)
      Builtin Implies :@: es  -> tell ([],init es) >> go True (last es)
      _                       -> return e0


-- | Negates the conjecture: changes assert-not into assert, and
--   introduce skolem types in case the goal is polymorphic.
--   (runs 'typeSkolemConjecture')
negateConjecture :: Name a => Theory a -> Fresh (Theory a)
negateConjecture = fmap (declsPass (map neg1)) . typeSkolemConjecture
  where
  neg1 (AssertDecl (Formula Prove n i [] form))
      = AssertDecl (Formula Assert n i [] (gentleNeg form))
  neg1 d0 = d0

-- | Introduce skolem types in case the goal is polymorphic.
typeSkolemConjecture :: Name a => Theory a -> Fresh (Theory a)
typeSkolemConjecture thy =
  foldM ty_skolem1
    thy { thy_asserts = filter (not . isProve) (thy_asserts thy) }
    (filter isProve (thy_asserts thy))
  where
  isProve (Formula Prove _ _ _ form) = True
  isProve _ = False

  ty_skolem1 thy (Formula Prove n i tvs form) = do
    tvs' <- mapM (refreshNamed "sk_") tvs
    return thy {
      thy_asserts = Formula Prove n i [] (makeTyCons (zip tvs tvs') form):thy_asserts thy,
      thy_sorts = [ Sort tv [] | tv <- tvs' ] ++ thy_sorts thy }

  makeTyCons tvs =
    transformTypeInExpr $ \ty ->
      case ty of
        TyVar tv | Just tv' <- lookup tv tvs -> TyCon tv' []
        _ -> ty
