{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.CommuteMatch where

#include "errors.h"
import Tip.Core
import Tip.Fresh
import Tip.Simplify
import Tip.Scope

import Data.Generics.Geniplate
import Control.Applicative
import Data.Maybe

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
