{-# LANGUAGE ScopedTypeVariables #-}
module Props where

import Prelude hiding ((==))
import Tip

data A = A | B | C deriving (Eq,Show)
A == A = True
B == B = True
C == C = True
_ == _ = False

prop_or1 (a :: A) b =       a === b  .||.       b === a
prop_or2 (a :: A) b = bool (a ==  b) .||.       b === a
prop_or3 (a :: A) b =       a === b  .||. bool (b ==  a)

prop_and1 (a :: A) b =       a === b  .&&. b === a
prop_and2 (a :: A) b = bool (a ==  b) .&&. b === a
prop_and3 (a :: A) b =       a === b  .&&. bool (b == a)

prop_imp1 (a :: A) b =       a === b  ==> b === a
prop_imp2 (a :: A) b = bool (a ==  b) ==> b === a
prop_imp3 (a :: A) b =       a === b  ==> bool (b == a)

prop_neg1 (a :: A) b = neg       (a === b)
prop_neg2 (a :: A) b = neg (bool (a ==  b))

prop_quantifiers1 = exists (\ a -> forAll (\ (b :: A) -> a === b))

prop_quantifiers2 = forAll (\ a -> exists (\ (b :: A) -> a === b))

