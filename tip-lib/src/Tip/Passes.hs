-- | Passes
module Tip.Passes
  (
  -- * Running passes in the Fresh monad
    freshPass

  -- * Simplifications
  , simplifyTheory, gently, aggressively, SimplifyOpts(..)
  , removeNewtype
  , uncurryTheory

  -- * Simplifyng conjectures
  , module Tip.Pass.Conjecture

  -- * Changing status of conjectures
  , makeConjecture
  , selectConjecture
  , provedConjecture
  , deleteConjecture

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
  , axiomatizeFuncdefs2

  -- * Data types
  , axiomatizeDatadecls

  -- * Monomorphisation
  , monomorphise

  -- * Induction
  , induction

  -- * Miscellaneous
  , dropSuffix

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
import Tip.Pass.Conjecture
import Tip.Pass.EqualFunctions
import Tip.Pass.Lift
import Tip.Pass.Monomorphise
import Tip.Pass.Booleans
import Tip.Pass.EliminateDeadCode
import Tip.Pass.FillInCases
import Tip.Pass.AxiomatizeFuncdefs
import Tip.Pass.AxiomatizeDatadecls
import Tip.Pass.Min
import Tip.Pass.SelectConjecture
import Tip.Pass.DropSuffix
import Tip.Pass.Induction

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
  | SplitConjecture
  | SkolemiseConjecture
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
  | AxiomatizeFuncdefs2
  | AxiomatizeDatadecls
  | Min
  | Monomorphise Bool
  | CSEMatch
  | CSEMatchWhy3
  | EliminateDeadCode
  | MakeConjecture Int
  | SelectConjecture Int
  | ProvedConjecture Int
  | DeleteConjecture Int
  | DropSuffix String
  | Induction [Int]
 deriving (Eq,Ord,Show,Read)

instance Pass StandardPass where
  passName = show
  runPass p = case p of
    SimplifyGently       -> single $ simplifyTheory gently
    SimplifyAggressively -> single $ simplifyTheory aggressively
    RemoveNewtype        -> single $ return . removeNewtype
    UncurryTheory        -> single $ uncurryTheory
    NegateConjecture     -> single $ negateConjecture
    TypeSkolemConjecture -> single $ typeSkolemConjecture
    SplitConjecture      -> return . splitConjecture
    SkolemiseConjecture  -> skolemiseConjecture
    IfToBoolOp           -> single $ return . ifToBoolOp
    BoolOpToIf           -> single $ return . theoryBoolOpToIf
    AddMatch             -> single $ addMatch
    CommuteMatch         -> single $ commuteMatchTheory
    RemoveMatch          -> single $ removeMatch
    CollapseEqual        -> single $ return . collapseEqual
    RemoveAliases        -> single $ return . removeAliases
    LambdaLift           -> single $ lambdaLift
    LetLift              -> single $ letLift
    AxiomatizeLambdas    -> single $ axiomatizeLambdas
    AxiomatizeFuncdefs   -> single $ return . axiomatizeFuncdefs
    AxiomatizeFuncdefs2  -> single $ return . axiomatizeFuncdefs2 (const Nothing)
    AxiomatizeDatadecls  -> single $ axiomatizeDatadecls (const Nothing)
    Min                  -> single $ minPass
    Monomorphise b       -> single $ monomorphise b
    CSEMatch             -> single $ return . cseMatch cseMatchNormal
    CSEMatchWhy3         -> single $ return . cseMatch cseMatchWhy3
    EliminateDeadCode    -> single $ return . eliminateDeadCode
    MakeConjecture n     -> single $ return . makeConjecture n
    SelectConjecture n   -> single $ return . selectConjecture n
    ProvedConjecture n   -> single $ return . provedConjecture n
    DeleteConjecture n   -> single $ return . deleteConjecture n
    DropSuffix cs        -> single $ dropSuffix cs
    Induction coords     -> induction coords
    where single m thy = do x <- m thy; return [x]
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
      unitPass SplitConjecture $
        help "Puts goals in separate theories",
      unitPass SkolemiseConjecture $
        help "Skolemise the conjecture",
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
      unitPass AxiomatizeFuncdefs2 $
        help "Transform function definitions to axioms with left hand side pattern matching instead of match",
      unitPass AxiomatizeDatadecls $
        help "Transform data declarations to axioms",
      unitPass Min $
        help "Transform function and data declarations to axioms, using a ``min'' heuristic",
      flag' () (long ("monomorphise") <> help "Try to monomorphise the problem") *> pure (Monomorphise False),
      flag' () (long ("monomorphise-verbose") <> help "Try to monomorphise the problem verbosely") *> pure (Monomorphise True),
      unitPass CSEMatch $
        help "Perform CSE on match scrutinees",
      unitPass CSEMatchWhy3 $
        help "Aggressively perform CSE on match scrutinees (helps Why3's termination checker)",
      unitPass EliminateDeadCode $
        help "Dead code elimination (doesn't work on dead recursive functions)",
      fmap MakeConjecture $
        option auto $
          long "make-conjecture" <>
          metavar "CONJECTURE-NUMBER" <>
          help "Make an assert into an assert-not",
      fmap SelectConjecture $
        option auto $
          long "select-conjecture" <>
          metavar "CONJECTURE-NUMBER" <>
          help "Choose a particular conjecture from the problem",
      fmap ProvedConjecture $
        option auto $
          long "proved-conjecture" <>
          metavar "CONJECTURE-NUMBER" <>
          help "Mark a particular conjecture as proved",
      fmap DeleteConjecture $
        option auto $
          long "delete-conjecture" <>
          metavar "CONJECTURE-NUMBER" <>
          help "Delete a particular conjecture",
      fmap DropSuffix $
        option str $
          long "drop-suffix" <>
          metavar "SUFFIX-CHARS" <>
          help "Drop the suffix delimited by some character set",
      fmap Induction $
        option auto $
          long "induction" <>
          metavar "VAR-COORD" <>
          help "Perform induction on the variable coordinates"
      ]
