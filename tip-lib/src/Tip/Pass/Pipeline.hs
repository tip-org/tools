module Tip.Pass.Pipeline where

import Tip.Lint
import Tip.Types (Theory)

import Tip.Utils

import Tip.Fresh


import Data.List (intercalate)
import Data.Either (partitionEithers)
import Control.Monad ((>=>))

class Pass p where
  runPass  :: Name a => p -> Theory a -> Fresh (Theory a)
  passName :: p -> String

runPassLinted :: (Pass p, Name a) => p -> Theory a -> Fresh (Theory a)
runPassLinted p = runPass p >=> lintM (passName p)

-- | A sum type that supports 'Enum' and 'Bounded'
data Choice a b = First a | Second b
  deriving (Eq,Ord,Show)

-- | 'either' for 'Choice'
choice :: (a -> c) -> (b -> c) -> Choice a b -> c
choice f _ (First x)  = f x
choice _ g (Second y) = g y

instance (Pass a, Pass b) => Pass (Choice a b) where
  passName = choice passName passName
  runPass = choice runPass runPass

instance (Enum a, Enum b, Bounded a) => Enum (Choice a b) where
  toEnum i
    | i >= numElements x = Second (toEnum (i - numElements x))
    | otherwise          = first_res
   where
    first_res  = First (toEnum i)
    ~(First x) = first_res

  fromEnum xy =
    case xy of
      First x  -> fromEnum x
      Second y -> fromEnum y + numElements x
   where ~(First x) = xy

-- | All the elements in an enumeration
elements :: (Enum a,Bounded a) => [a]
elements = [minBound..maxBound]

-- | The number of elements in an enumeration
numElements :: (Enum a,Bounded a) => a -> Int
numElements x = length (elements `asTypeOf` [x])

instance (Bounded a, Bounded b) => Bounded (Choice a b) where
  minBound = First  minBound
  maxBound = Second maxBound

runPasses :: (Pass p,Name a) => [p] -> Theory a -> Fresh (Theory a)
runPasses = go []
 where
  go _    [] = return
  go past (p:ps) =
        runPass p
    >=> lintM (passName p ++ "(and " ++ intercalate "," past ++ ")")
    >=> go (passName p:past) ps

parsePass :: (Enum p,Bounded p,Pass p) => String -> Maybe p
parsePass s =
  lookup s (concat
    [ [ (passName p,p)
      , (flagify (passName p),p) ]
    | p <- elements ])

parsePasses :: (Enum p,Bounded p,Pass p) => [String] -> ([p],[String])
parsePasses = partitionEithers . map (\ s -> maybe (Right s) Left (parsePass s))

