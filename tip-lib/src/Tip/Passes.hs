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
  , typeSkolemConjecture

  -- * Boolean builtins
  , ifToBoolOp
  , boolOpToIf
  , theoryBoolOpToIf

  -- * Match expressions
  , addMatch
  , commuteMatch
  , removeMatch
  , cseMatch
  , cseMatchNormal
  , cseMatchWhy3
  , fillInCases

  -- * Duplicated functions
  , collapseEqual
  , removeAliases

  -- * Lambda and let lifting
  , lambdaLift
  , letLift
  , axiomatizeLambdas

  -- * Function definitions
  , axiomatizeFuncdefs

  -- * Monomorphisation
  , monomorphise

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
import Tip.Pass.Monomorphise
import Tip.Pass.Booleans
import Tip.Pass.EliminateDeadCode
import Tip.Pass.FillInCases
import Tip.Pass.AxiomatizeFuncdefs

import Tip.Fresh

import Tip.Pass.Pipeline

import Options.Applicative

-- | The passes in the standard Tip distribution
data StandardPass
  = SimplifyGently
  | SimplifyAggressively
  | RemoveNewtype
  | UncurryTheory
  | NegateConjecture
  | TypeSkolemConjecture
  | IfToBoolOp
  | BoolOpToIf
  | AddMatch
  | CommuteMatch
  | RemoveMatch
  | CollapseEqual
  | RemoveAliases
  | LambdaLift
  | LetLift
  | AxiomatizeLambdas
  | AxiomatizeFuncdefs
  | Monomorphise
  | CSEMatch
  | CSEMatchWhy3
  | EliminateDeadCode
 deriving (Eq,Ord,Show,Read,Enum,Bounded)

instance Pass StandardPass where
  passName = show
  runPass p = case p of
    SimplifyGently       -> simplifyTheory gently
    SimplifyAggressively -> simplifyTheory aggressively
    RemoveNewtype        -> return . removeNewtype
    UncurryTheory        -> uncurryTheory
    NegateConjecture     -> negateConjecture
    TypeSkolemConjecture -> typeSkolemConjecture
    IfToBoolOp           -> return . ifToBoolOp
    BoolOpToIf           -> return . theoryBoolOpToIf
    AddMatch             -> addMatch
    CommuteMatch         -> commuteMatch
    RemoveMatch          -> removeMatch
    CollapseEqual        -> return . collapseEqual
    RemoveAliases        -> return . removeAliases
    LambdaLift           -> lambdaLift
    LetLift              -> letLift
    AxiomatizeLambdas    -> axiomatizeLambdas
    AxiomatizeFuncdefs   -> return . axiomatizeFuncdefs
    Monomorphise         -> monomorphise
    CSEMatch             -> return . cseMatch cseMatchNormal
    CSEMatchWhy3         -> return . cseMatch cseMatchWhy3
    EliminateDeadCode    -> return . eliminateDeadCode
  parsePass =
    foldr (<|>) empty [
      unitPass SimplifyGently $
        help "Simplify the problem, trying not to increase its size",
      unitPass SimplifyAggressively $
        help "Simplify the problem even at the cost of making it bigger",
      unitPass RemoveNewtype $
        help "Eliminate single-constructor, single-argument datatypes",
      unitPass UncurryTheory $
        help "Eliminate unnecessary use of higher-order functions",
      unitPass NegateConjecture $
        help "Transform the goal into a negated conjecture",
      unitPass TypeSkolemConjecture $
        help "Skolemise the types in the conjecutre",
      unitPass IfToBoolOp $
        help "Replace if-then-else by and/or where appropriate",
      unitPass BoolOpToIf $
        help "Replace and/or by if-then-else",
      unitPass AddMatch $
        help "Transform SMTLIB-style datatype access into pattern matching",
      unitPass CommuteMatch $
        help "Eliminate matches that occur in weird positions (e.g. as arguments to function calls)",
      unitPass RemoveMatch $
        help "Replace pattern matching with SMTLIB-style datatype access",
      unitPass CollapseEqual $
        help "Merge functions with equal definitions",
      unitPass RemoveAliases $
        help "Eliminate any function defined simply as f(x) = g(x)",
      unitPass LambdaLift $
        help "Lift lambdas to the top level",
      unitPass LetLift $
        help "Lift let-expressions to the top level",
      unitPass AxiomatizeLambdas $
        help "Eliminate lambdas by axiomatisation (requires --lambda-lift)",
      unitPass AxiomatizeFuncdefs $
        help "Transform function definitions to axioms in the most straightforward way",
      unitPass Monomorphise $
        help "Try to monomorphise the problem",
      unitPass CSEMatch $
        help "Perform CSE on match scrutinees",
      unitPass CSEMatchWhy3 $
        help "Aggressively perform CSE on match scrutinees (helps Why3's termination checker)",
      unitPass EliminateDeadCode $
        help "Dead code elimination (doesn't work on dead recursive functions)"]
