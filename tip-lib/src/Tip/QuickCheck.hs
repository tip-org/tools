{-# LANGUAGE RecordWildCards, FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
module Tip.QuickCheck where

import Tip.Core
import Tip.Eval
import Tip.Pretty
import Test.QuickCheck
import Test.QuickCheck.Gen.Unsafe
import Data.Reflection
import qualified Data.Map.Strict as Map
import Control.Spoon

instance Given (Theory a) => CoArbitrary (Value a) where
  coarbitrary (IntVal x) = variant 0 . coarbitrary x
  coarbitrary (RatVal x) = variant 1 . coarbitrary x
  coarbitrary (BoolVal x) = variant 2 . coarbitrary x
  coarbitrary (FuncVal (args :=>: _) f) = variant 3 . coarb
    where
      -- Adapted from CoArbitrary (a -> b)
      coarb gen = do
        xss <- listOf (mapM (genTerm given) args)
        coarbitrary (map f xss) gen
  coarbitrary (ConVal _ n _ xs) = variant 4 . coarbitrary n . coarbitrary xs

genTerm :: Theory a -> Type a -> Gen (Value a)
genTerm = undefined

-- genFunc :: (Ord a, CoArbitrary a) => Theory a -> Gen ((Global a, [Value a]) -> Value a)
-- genFunc thy = give thy (arbitraryFunction (\(gbl, _) -> genTerm thy (snd (gblType gbl))))

-- evalQC :: (Ord a, CoArbitrary a) => Theory a -> Gen (Evaluator a)
-- evalQC thy = do
--   func <- genFunc thy
--   return Evaluator {
--     eval_uninterpreted = \gbl vs -> func (gbl, vs) }

-- tipCheck :: (Ord a, CoArbitrary a, PrettyVar a) => Theory a -> Expr a -> IO Result
-- tipCheck thy = quickCheckResult . test Map.empty
--   where
--     test env (Quant _ Forall xs e) =
--       forAll (Blind <$> (mapM (genTerm thy . lcl_type) xs)) $
--         \(Blind vs) -> test (Map.union env (Map.fromList (zip (map lcl_name xs) vs))) e
--     test env (Quant _ Exists _ _) = discard
--     test env e =
--       forAll (Blind <$> evalQC thy) $
--         \(Blind ev) ->
--           case teaspoon (eval ev thy env e) of
--             Just (BoolVal x) -> x
--             _ -> discard

-- tipCheckAll :: (Ord a, CoArbitrary a, PrettyVar a) => Theory a -> IO (Theory a)
-- tipCheckAll thy = do
--   asserts <- mapM go (thy_asserts thy)
--   return thy { thy_asserts = asserts }
--   where
--     go form@Formula{fm_role = Prove, ..} = do
--       res <- tipCheck thy fm_body
--       case res of
--         Success{} -> return (putAttr tested () form)
--         Failure{} -> return (putAttr falsified () form)
--         _ -> return form
--     go form = return form

-- | Generate a random function. Should be in QuickCheck.
arbitraryFunction :: CoArbitrary a => (a -> Gen b) -> Gen (a -> b)
arbitraryFunction gen = promote (\x -> coarbitrary x (gen x))
