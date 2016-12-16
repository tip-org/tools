{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.CommuteMatch where

#include "errors.h"
import Tip.Core
import Tip.Fresh
import Tip.Simplify
import Tip.Scope

import Data.Generics.Geniplate
import Data.Maybe
import Control.Monad

-- | Makes an effort to move match statements upwards: moves match above
-- function applications, and moves matches inside scrutinees outside.
--
-- Does not move past quantifiers, lets, and lambdas.
commuteMatchTheory :: Name a => Theory a -> Fresh (Theory a)
commuteMatchTheory thy = commuteMatch (Just thy) thy

-- | Makes an effort to move match statements upwards: moves match above
-- function applications, and moves matches inside scrutinees outside.
--
-- Does not move past quantifiers, lets, and lambdas.
commuteMatch :: forall a f. (Name a, TransformBiM Fresh (Expr a) (f a)) => Maybe (Theory a) -> f a -> Fresh (f a)
commuteMatch mthy = aux
  where
    aux :: forall f. (TransformBiM Fresh (Expr a) (f a)) => f a -> Fresh (f a)
    aux = transformExprInM $ \e0 ->
      case e0 of
        Match (Match e inner_alts) outer_alts ->
          aux =<< do
            Match e <$> sequence
              [ Case lhs <$> freshen (match rhs outer_alts)
              | Case lhs rhs <- inner_alts
              ]

        Match e alts | Just e' <- toMatch e ->
          aux (Match e' alts)

        hd :@: args
          | and [ not (logicalBuiltin b) | Builtin b <- [hd] ]
          , let isMatch Match{} = True
                isMatch _       = False
          , (left, Match e alts:right) <- break isMatch args
          -> aux =<< do
               Match e <$> sequence
                 [ Case lhs <$> freshen (hd :@: (left ++ [rhs] ++ right))
                 | Case lhs rhs <- alts
                 ]

        Lam bs e  -> Lam bs <$> aux e

        Quant qi q bs e -> Quant qi q bs <$> aux e

        Let x b e -> Let x b <$> aux e

        _ -> return e0

    mscp = fmap scope mthy
    match e cases = fromMaybe (Match e cases) (tryMatch mscp e cases)

    -- Turn e.g. (= x nil) into a match.
    toMatch :: Expr a -> Maybe (Expr a)
    toMatch (Builtin eq :@: [t, u])
      | eq `elem` [Equal, Distinct] =
        toMatch1 eq t u `mplus` toMatch1 eq u t
    toMatch _ = Nothing

    toMatch1 eq t u | Just pat <- toPattern u =
      Just $
        Match t
          [Case Default (bool (if eq == Equal then False else True)),
            Case pat (bool (if eq == Equal then True else False))]
    toMatch1 _ _ _ = Nothing

    toPattern (Gbl gbl@Global{..} :@: [])
      | Just scp <- mscp,
        Just (d, c) <- lookupConstructor gbl_name scp =
        Just (ConPat gbl [])
    toPattern (Builtin (Lit l) :@: []) =
      Just (LitPat l)
    toPattern _ = Nothing
