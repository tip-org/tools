{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.Pipeline where

import Tip.Lint
import Tip.Types (Theory)

import Tip.Utils

import Tip.Fresh


import Data.List (intercalate)
import Data.Either (partitionEithers)
import Control.Monad ((>=>))
import Options.Applicative

class Pass p where
  runPass   :: Name a => p -> Theory a -> Fresh [Theory a]
  passName  :: p -> String
  parsePass :: Parser p

unitPass :: Pass p => p -> Mod FlagFields () -> Parser p
unitPass p mod = flag' () (long (flagify (passName p)) <> mod) *> pure p

lintMany :: (Name a,Monad m) => String -> [Theory a] -> m [Theory a]
lintMany s thys = mapM (lintM s) thys

runPassLinted :: (Pass p,Name a) => p -> Theory a -> Fresh [Theory a]
runPassLinted p = runPass p >=> lintMany (passName p)

-- | A sum type that supports 'Enum' and 'Bounded'
data Choice a b = First a | Second b
  deriving (Eq,Ord,Show)

-- | 'either' for 'Choice'
choice :: (a -> c) -> (b -> c) -> Choice a b -> c
choice f _ (First x)  = f x
choice _ g (Second y) = g y

instance (Pass a, Pass b) => Pass (Choice a b) where
  passName  = choice passName passName
  runPass   = choice runPass runPass
  parsePass = (First <$> parsePass) <|> (Second <$> parsePass)

runPasses :: (Pass p,Name a) => [p] -> Theory a -> Fresh [Theory a]
runPasses ps = continuePasses ps . return

continuePasses :: forall p a . (Pass p,Name a) => [p] -> [Theory a] -> Fresh [Theory a]
continuePasses = go []
 where
  go :: [String] -> [p] -> [Theory a] -> Fresh [Theory a]
  go _    []     = return
  go past (p:ps) =
        (fmap concat . mapM (runPass p))
    >=> lintMany (passName p ++ (if null past then "" else "(after " ++ intercalate "," past ++ ")"))
    >=> go (passName p:past) ps

parsePasses :: Pass p => Parser [p]
parsePasses = many parsePass
