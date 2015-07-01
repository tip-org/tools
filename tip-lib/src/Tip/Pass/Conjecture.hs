{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
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
    [Formula Prove tvs body] ->
      case tvs of
        [] -> do let (body',sks) = runWriter (skolemise body)
                 sks' <- mapM refreshLocal sks
                 body'' <- substMany (sks `zip` map Lcl sks') body'
                 return thy {
                       thy_sigs    = map local_signature sks' ++ thy_sigs thy,
                       thy_asserts = Formula Prove [] body'' : assums
                     }
        _ -> ERROR("Cannot skolemise conjecture with type variables")
    _ -> ERROR("Need one co:jecture to skolemise conjecture")
  where
  (goals,assums) = theoryGoals thy

  local_signature :: Local b -> Signature b
  local_signature (Local v t) = Signature v (PolyType [] [] t)

skolemise :: Expr a -> Writer [Local a] (Expr a)
skolemise e0
  = case e0 of
      Quant qi Forall lcls e -> tell lcls >> skolemise e
      Builtin Not :@: [e]    -> skolemise (neg e)
      Builtin Implies :@: es -> do e' <- skolemise (last es)
                                   return (Builtin Implies :@: (init es ++ [e']))
      _ -> return e0
 

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
