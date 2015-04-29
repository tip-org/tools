-- Passes
module Tip.Passes
  (
  -- * Running passes in the Fresh monad
    freshPass

  -- * Simplifications
  , simplifyTheory, gently, aggressively, SimplifyOpts(..)
  , denewtype
  , delambda
  , deprove

  -- * Match expressions
  , addCase
  , commuteMatch
  , decase

  -- * Duplicated functions
  , collapseEqual
  , removeAliases

  -- * Lambda and let lifting
  , lambdaLift
  , letLift
  , axiomatizeLambdas
  ) where

import Tip.Simplify

import Tip.Fresh

import Tip.Pass.AddCase
import Tip.Pass.CommuteMatch
import Tip.Pass.Decase
import Tip.Pass.Delambda
import Tip.Pass.Denewtype
import Tip.Pass.Deprove
import Tip.Pass.EqualFunctions
import Tip.Pass.Lift

