-- | Passes
module Tip.Passes
  (
  -- * Running passes in the Fresh monad
    freshPass

  -- * Simplifications
  , simplifyTheory, gently, aggressively, SimplifyOpts(..)
  , removeNewtype
  , uncurryTheory

  -- * Simplifying conjectures
  , module Tip.Pass.Conjecture
  , module Tip.Pass.Concretise

  -- * Changing status of conjectures
  , makeConjecture
  , selectConjecture
  , provedConjecture
  , deleteConjecture

  -- * Boolean builtins
  , ifToBoolOp
  , boolOpToIf
  , theoryBoolOpToIf
  , removeBuiltinBool
  , boolOpLift

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
  , eliminateLetRec
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
  , recursionInduction

  -- * Miscellaneous
  , uniqLocals
  , dropSuffix
  , dropAttributes

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
import Tip.Pass.Concretise
import Tip.Pass.EqualFunctions
import Tip.Pass.Lift
import Tip.Pass.Monomorphise
import Tip.Pass.Booleans
import Tip.Pass.EliminateDeadCode
import Tip.Pass.FillInCases
import Tip.Pass.AxiomatizeFuncdefs
import Tip.Pass.AxiomatizeDatadecls
import Tip.Pass.SelectConjecture
import Tip.Pass.DropSuffix
import Tip.Pass.UniqLocals
import Tip.Pass.Induction
import Tip.Pass.DropAttributes

import Tip.Fresh

import Tip.Pass.Pipeline

import Options.Applicative
import Data.Monoid ((<>))

-- | The passes in the standard Tip distribution
data StandardPass
  = SimplifyGently
  | SimplifyAggressively
  | RemoveNewtype
  | UncurryTheory
  | NegateConjecture
  | TypeSkolemConjecture
  | IntToNat
  | SortsToNat
  | SplitConjecture
  | SkolemiseConjecture
  | IfToBoolOp
  | BoolOpToIf
  | RemoveBuiltinBool
  | BoolOpLift
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
  | AxiomatizeDatadeclsUEQ
  | Monomorphise Bool
  | CSEMatch
  | CSEMatchWhy3
  | EliminateDeadCode
  | MakeConjecture Int
  | SelectConjecture Int
  | ProvedConjecture Int
  | DeleteConjecture Int
  | DropSuffix String
  | UniqLocals
  | DropAttributes
  | Induction [Int]
  | RecursionInduction Int [Int]
 deriving (Eq,Ord,Show,Read)

instance Pass StandardPass where
  passName = show
  runPass p = case p of
    SimplifyGently       -> single $ simplifyTheory gently
    SimplifyAggressively -> single $ simplifyTheory aggressively
    RemoveNewtype        -> single $ return . removeNewtype
    UncurryTheory        -> single $ uncurryTheory
    NegateConjecture     -> (return . splitConjecture) `followedBy` single negateConjecture
    TypeSkolemConjecture -> single $ typeSkolemConjecture
    IntToNat             -> single $ intToNat
    SortsToNat           -> single $ sortsToNat
    SplitConjecture      -> return . splitConjecture
    SkolemiseConjecture  -> skolemiseConjecture
    IfToBoolOp           -> single $ return . ifToBoolOp
    BoolOpToIf           -> single $ return . theoryBoolOpToIf
    RemoveBuiltinBool    -> single $ removeBuiltinBool
    BoolOpLift           -> single $ boolOpLift
    AddMatch             -> single $ addMatch
    CommuteMatch         -> single $ commuteMatchTheory
    RemoveMatch          -> single $ removeMatch
    CollapseEqual        -> single $ return . removeAliases . collapseEqual
    RemoveAliases        -> single $ return . removeAliases
    LambdaLift           -> single $ lambdaLift
    LetLift              -> single $ letLift
    AxiomatizeLambdas    -> single lambdaLift `followedBy` single axiomatizeLambdas
    AxiomatizeFuncdefs   -> single $ return . axiomatizeFuncdefs
    AxiomatizeFuncdefs2  -> single $ return . axiomatizeFuncdefs2
    AxiomatizeDatadecls    -> single $ axiomatizeDatadecls False
    AxiomatizeDatadeclsUEQ -> single $ axiomatizeDatadecls True
    Monomorphise b       -> single typeSkolemConjecture `followedBy` single (monomorphise b)
    CSEMatch             -> single $ return . cseMatch cseMatchNormal
    CSEMatchWhy3         -> single $ return . cseMatch cseMatchWhy3
    EliminateDeadCode    -> single $ return . eliminateDeadCode
    MakeConjecture n     -> single $ return . makeConjecture n
    SelectConjecture n   -> single $ return . selectConjecture n
    ProvedConjecture n   -> single $ return . provedConjecture n
    DeleteConjecture n   -> single $ return . deleteConjecture n
    DropSuffix cs        -> single $ dropSuffix cs
    UniqLocals           -> single $ uniqLocals
    DropAttributes       -> single $ return . dropAttributes
    Induction coords     -> induction coords
    RecursionInduction fn xsns -> recursionInduction fn xsns
    where
      single m thy = do x <- m thy; return [x]
      f `followedBy` g = \thy -> do
        thys <- f thy
        fmap concat (mapM g thys)
      
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
        help "Skolemise the types in the conjecture",
      unitPass IntToNat $
        help "Replace builtin Integer with a a unary nat datatype nat (if only ordering is used)",
      unitPass SortsToNat $
        help "Replace abstract sorts with a unary nat datatype.",
      unitPass SplitConjecture $
        help "Puts goals in separate theories",
      unitPass SkolemiseConjecture $
        help "Skolemise the conjecture",
      unitPass IfToBoolOp $
        help "Replace if-then-else by and/or where appropriate",
      unitPass BoolOpToIf $
        help "Replace and/or by if-then-else",
      unitPass RemoveBuiltinBool $
        help "Replace the builtin bool with a datatype",
      unitPass BoolOpLift $
        help "Lift boolean operators to the top level",
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
        help "Eliminate lambdas by axiomatisation",
      unitPass AxiomatizeFuncdefs $
        help "Transform function definitions to axioms in the most straightforward way",
      unitPass AxiomatizeFuncdefs2 $
        help "Transform function definitions to axioms with left hand side pattern matching instead of match",
      unitPass AxiomatizeDatadecls $
        help "Transform data declarations to axioms",
      unitPass AxiomatizeDatadeclsUEQ $
        help "Transform data declarations to unit equality axioms (incomplete)",
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
      unitPass UniqLocals $
        help "Make all local variables unique",
      unitPass DropAttributes $
        help "Remove all attributes (e.g. :keep) from declarations",
      fmap Induction $
        option auto $
          long "induction" <>
          metavar "VAR-COORD" <>
          help "Perform induction on the variable coordinates",
      fmap (uncurry RecursionInduction) $
        option auto $
          long "ri" <>
          metavar "COORDS" <>
          help "Perform recursion induction"
      ]
