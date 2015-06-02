-- | Passes
module Tip.Passes
  (
  -- * Running passes in the Fresh monad
    freshPass

  -- * Simplifications
  , simplifyTheory, gently, aggressively, SimplifyOpts(..)
  , removeNewtype
  , uncurryTheory
  , negateConjecture

  -- * Boolean builtins
  , ifToBoolOp
  , boolOpToIf

  -- * Match expressions
  , addMatch
  , commuteMatch
  , removeMatch
  , cseMatch
  , cseMatchNormal
  , cseMatchWhy3

  -- * Duplicated functions
  , collapseEqual
  , removeAliases

  -- * Lambda and let lifting
  , lambdaLift
  , letLift
  , axiomatizeLambdas

  -- * Building pass pipelines
  , StandardPass(..)
  , module Tip.Pass.Pipeline
  ) where

import Tip.Simplify

import Tip.Pass.AddMatch
import Tip.Pass.CommuteMatch
import Tip.Pass.RemoveMatch
import Tip.Pass.CSEMatch
import Tip.Pass.Uncurry
import Tip.Pass.RemoveNewtype
import Tip.Pass.NegateConjecture
import Tip.Pass.EqualFunctions
import Tip.Pass.Lift
import Tip.Pass.Booleans

import Tip.Fresh

import Tip.Pass.Pipeline

-- | The passes in the standard Tip distribution
data StandardPass
  = SimplifyGently
  | SimplifyAggressively
  | RemoveNewtype
  | UncurryTheory
  | NegateConjecture
  | IfToBoolOp
  | AddMatch
  | CommuteMatch
  | RemoveMatch
  | CollapseEqual
  | RemoveAliases
  | LambdaLift
  | LetLift
  | AxiomatizeLambdas
  | CSEMatch
  | CSEMatchWhy3
 deriving (Eq,Ord,Show,Enum,Bounded)

instance Pass StandardPass where
  passName = show
  runPass p = case p of
    SimplifyGently       -> simplifyTheory gently
    SimplifyAggressively -> simplifyTheory aggressively
    RemoveNewtype     -> return . removeNewtype
    UncurryTheory     -> uncurryTheory
    NegateConjecture  -> negateConjecture
    IfToBoolOp        -> return . ifToBoolOp
    AddMatch          -> addMatch
    CommuteMatch      -> commuteMatch
    RemoveMatch       -> removeMatch
    CollapseEqual     -> return . collapseEqual
    RemoveAliases     -> return . removeAliases
    LambdaLift        -> lambdaLift
    LetLift           -> letLift
    AxiomatizeLambdas -> axiomatizeLambdas
    CSEMatch          -> return . cseMatch cseMatchNormal
    CSEMatchWhy3      -> return . cseMatch cseMatchWhy3
