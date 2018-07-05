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

-- | Splits a theory with many goals into many theories each with one goal
splitConjecture :: Theory a -> [Theory a]
splitConjecture thy =
  [ thy { thy_asserts = goal : assums } | goal <- goals ]
  where
  (goals,assums) = theoryFormulas thy

-- | Splits, type skolems and skolemises conjectures!
skolemiseConjecture :: Name a => Theory a -> Fresh [Theory a]
skolemiseConjecture = mapM (skolemiseConjecture' <=< typeSkolemConjecture ModeConjecture) . splitConjecture

-- | Skolemises a conjecture, assuming that there is just one goal and that it has no type variables.
skolemiseConjecture' :: Name a => Theory a -> Fresh (Theory a)
skolemiseConjecture' thy =
  case goals of
    [Formula Prove attrs tvs body] ->
      case tvs of
        [] -> do let (body',(sks,pre)) = runWriter (skolemise body)

                 sks' <- sequence
                   [ do v' <- refresh v
                        return $
                          putAttr skolem () $
                          Signature v' [] (PolyType [] [] t)
                   | Local v t <- sks
                   ]

                 let su = substMany (sks `zip` map (\ sk -> applySignature sk [] []) sks')

                 body'' <- su body'

                 pre'' <- mapM su pre

                 return thy {
                       thy_sigs    = sks' ++ thy_sigs thy,
                       thy_asserts = Formula Prove attrs [] body'' : map (formula Assert attrs []) pre'' ++ assums
                     }
        _ -> ERROR("Cannot skolemise conjecture with type variables")
    _ -> ERROR("Need one conjecture to skolemise conjecture")
  where
  (goals,assums) = theoryFormulas thy

  formula r attrs tvs (Quant (QuantIH i) q vs e) =
    putAttr inductionHypothesis i $
    Formula r attrs tvs (mkQuant q vs e)
  formula r attrs tvs e = Formula r attrs tvs e

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
negateConjecture = fmap checkOneGoal . fmap (declsPass (map neg1)) . typeSkolemConjecture ModeConjecture
  where
  neg1 (AssertDecl (Formula Prove attrs [] form))
      = AssertDecl (Formula Assert attrs [] (gentleNeg form))
  neg1 d0 = d0

  checkOneGoal thy
    | length (theoryGoals thy) <= 1 = thy
    | otherwise = error "negateConjecture: more than one conjecture (try --split-conjecture first)"

data Mode = ModeConjecture | ModeMonomorphise deriving Eq

-- | Introduce skolem types in case the goal is polymorphic.
typeSkolemConjecture :: Name a => Mode -> Theory a -> Fresh (Theory a)
typeSkolemConjecture mode thy
  | all null (map fm_tvs (theoryGoals thy)),
    (case mode of
       ModeConjecture -> True
       ModeMonomorphise -> not (null (theoryGoals thy))) =
    return thy
  | otherwise = do
    tv <- freshNamed "sk"
    return thy {
      thy_sorts = putAttr skolem () (Sort tv [] []):thy_sorts thy,
      thy_asserts = map (ty_skolem1 tv) (thy_asserts thy) }
  where
  ty_skolem1 tv (Formula Prove attrs tvs form) =
      Formula Prove attrs [] (makeTyCons (zip tvs (repeat tv)) form)
  ty_skolem1 _ form@Formula{fm_role = Assert} = form

  makeTyCons tvs =
    transformTypeInExpr $ \ty ->
      case ty of
        TyVar tv | Just tv' <- lookup tv tvs -> TyCon tv' []
        _ -> ty
