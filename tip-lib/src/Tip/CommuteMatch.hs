{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
module Tip.CommuteMatch where

#include "errors.h"
import Tip
import Tip.Fresh
import Tip.Pretty

import Data.Generics.Geniplate
import Control.Applicative

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

    Lam{}   -> ERROR("Lam: " ++ ppRender e0)

    Let x b e -> Let x b <$> commuteMatch e

    _ -> return e0

