module Tip.GHC.Params where

import Options.Applicative

import Tip.Utils

import Data.List.Split
import Data.Monoid

-- | Parameters
data Params = Params
  { param_include     :: [FilePath]
  -- ^ Directories to include
  , param_debug_flags :: [DebugFlag]
  -- ^ Debugging flags
  , param_keep :: Maybe [String]
  -- ^ Only consider these functions and properties
  , param_counterexample_booleans :: Bool
  , param_no_iteB :: Bool
  }
  deriving Show

commaSep :: [String] -> [String]
commaSep = concatMap (splitOn ",")

parseParams :: Parser Params
parseParams =
  Params <$>
    param_include <*>
    param_debug_flags <*>
    param_keep <*>
    param_counterexample_booleans <*>
    param_no_iteB
  where
    param_include =
      many (strOption (long "include" <> short 'i' <> metavar "PATH" <> help "Extra include directory"))
    param_debug_flags =
      many $ foldr (<|>) empty
        [ flag' debug_flag (long (flagifyShow debug_flag) <> help (debugHelp debug_flag))
        | debug_flag <- [minBound..maxBound] ]
    param_keep =
      pure Nothing <|> fmap (Just . commaSep) (some (strOption keep_opt))

    keep_opt = long "keep" <> short 'k' <> metavar "NAME" <> help "Only keep these functions and properties (default all)"
    param_counterexample_booleans =
      switch (long "counterexample-booleans"
        <> help "Replace the built-in Bool datatype with the custom Boolean")
    param_no_iteB =
      switch (long "counterexample-no-iteB"
        <> help "Use match rather than iteB in the --counterexample-booleans translation")

-- | Default (empty) parameters
defaultParams :: Params
defaultParams = Params
  { param_include = []
  , param_debug_flags = []
  , param_keep = Nothing
  , param_counterexample_booleans = False
  , param_no_iteB = False
  }

-- | Debugging flags
data DebugFlag = PrintCore | PrintAllCore | PrintInitialTheory
  deriving (Eq,Show,Enum,Bounded)

debugHelp :: DebugFlag -> String
debugHelp PrintCore = "Print core bindings from GHC"
debugHelp PrintAllCore = "Print all core bindings from GHC, including external packages"
debugHelp PrintInitialTheory = "Print initial TIP theory"
