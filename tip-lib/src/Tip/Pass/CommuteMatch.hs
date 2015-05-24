{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
module Tip.Pass.CommuteMatch where

#include "errors.h"
import Tip.Core
import Tip.Fresh

import Data.Generics.Geniplate
import Control.Applicative

-- | Makes an effort to move match statements upwards: moves match above
-- function applications, and moves matches inside scrutinees outside.
--
-- Does not move past quantifiers, lets, and lambdas.
commuteMatch :: (Name a, TransformBiM Fresh (Expr a) (f a)) => f a -> Fresh (f a)
commuteMatch = transformExprInM $ \ e0 ->
  case e0 of
    Match (Match e inner_alts) outer_alts ->
      commuteMatch =<< do
        Match e <$> sequence
          [ Case lhs <$> freshen (Match rhs outer_alts)
          | Case lhs rhs <- inner_alts
          ]

    hd :@: args
      | and [ not (logicalBuiltin b) | Builtin b <- [hd] ]
      , let isMatch Match{} = True
            isMatch _       = False
      , (left, Match e alts:right) <- break isMatch args
      -> commuteMatch =<< do
           Match e <$> sequence
             [ Case lhs <$> freshen (hd :@: (left ++ [rhs] ++ right))
             | Case lhs rhs <- alts
             ]

    Lam bs e  -> Lam bs <$> commuteMatch e

    Quant qi q bs e -> Quant qi q bs <$> commuteMatch e

    Let x b e -> Let x b <$> commuteMatch e

    _ -> return e0

