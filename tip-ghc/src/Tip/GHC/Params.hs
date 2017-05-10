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
  }
  deriving Show

commaSep :: [String] -> [String]
commaSep = concatMap (splitOn ",")

parseParams :: Parser Params
parseParams =
  Params <$>
    param_include <*>
    param_debug_flags <*>
    param_keep
  where
    param_include =
      many (strOption (long "include" <> short 'i' <> metavar "PATH" <> help "Extra include directory"))
    param_debug_flags =
      many $ foldr (<|>) empty
        [ flag' debug_flag (long (flagifyShow debug_flag) <> help (debugHelp debug_flag))
        | debug_flag <- [minBound..maxBound] ]
    param_keep =
      pure Nothing <|> fmap (Just . commaSep) (many (strOption keep_opt))

    keep_opt = long "keep" <> short 'k' <> metavar "NAME" <> help "Only keep these functions and properties (default all)"

-- | Default (empty) parameters
defaultParams :: Params
defaultParams = Params
  { param_include = []
  , param_debug_flags = []
  , param_keep = Nothing
  }

-- | Debugging flags
data DebugFlag = PrintCore | PrintAllCore | PrintInitialTheory
  deriving (Eq,Show,Enum,Bounded)

debugHelp :: DebugFlag -> String
debugHelp PrintCore = "Print core bindings from GHC"
debugHelp PrintAllCore = "Print all core bindings from GHC, including external packages"
debugHelp PrintInitialTheory = "Print initial TIP theory"
