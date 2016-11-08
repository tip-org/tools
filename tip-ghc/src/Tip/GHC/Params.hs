module Tip.GHC.Params where

import Options.Applicative

import Tip.Utils

import Data.List.Split

-- | Parameters
data Params = Params
  { param_include     :: [FilePath]
  -- ^ Directories to include
  , param_debug_flags :: [DebugFlag]
  -- ^ Debugging flags
  , param_prop_names :: Maybe [String]
  -- ^ Only consider these properties
  , param_extra_names :: [String]
  -- ^ Extra names to consider
  , param_keep_all_names :: Bool
  -- ^ Keep unused names
  }
  deriving Show

commaSep :: [String] -> [String]
commaSep = concatMap (splitOn ",")

parseParams :: Parser Params
parseParams =
  Params <$>
    param_include <*>
    param_debug_flags <*>
    param_prop_names <*>
    param_extra_names <*>
    param_keep_all_names
  where
    param_include =
      many (strOption (long "include" <> short 'i' <> metavar "PATH" <> help "Extra include directory"))
    param_debug_flags =
      many $ foldr (<|>) empty
        [ flag' debug_flag (long (flagifyShow debug_flag) <> help (debugHelp debug_flag))
        | debug_flag <- [minBound..maxBound] ]
    param_prop_names =
      pure Nothing <|> fmap (Just . commaSep) (many (strOption prop_opt))
    param_extra_names =
      fmap commaSep (many (strOption (long "extra" <> short 'e' <> metavar "NAME" <> help "Function declaration to add to theory")))
    param_keep_all_names =
      flag False True (long "keep-all-functions" <> help "Don't remove unused functions from the theory")

    prop_opt = long "only" <> long "prop" <> short 'p' <> metavar "NAME" <> help "Property declaration to consider (default all)"

-- | Default (empty) parameters
defaultParams :: Params
defaultParams = Params
  { param_include = []
  , param_debug_flags = []
  , param_prop_names = Nothing
  , param_extra_names = []
  , param_keep_all_names = False
  }

-- | Debugging flags
data DebugFlag = PrintCore | PrintAllCore | PrintInitialTheory
  deriving (Eq,Show,Enum,Bounded)

debugHelp :: DebugFlag -> String
debugHelp PrintCore = "Print core bindings from GHC"
debugHelp PrintAllCore = "Print all core bindings from GHC, including external packages"
debugHelp PrintInitialTheory = "Print initial TIP theory"
