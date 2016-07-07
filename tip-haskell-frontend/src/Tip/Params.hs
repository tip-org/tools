module Tip.Params where

import Options.Applicative

import Tip.Utils

import Data.List.Split

-- | Parameters
data Params = Params
  { include     :: [FilePath]
  -- ^ Directories to include
  , debug_flags :: [DebugFlag]
  -- ^ Debugging flags
  , prop_names :: Maybe [String]
  -- ^ Only consider these properties
  , extra_names :: [String]
  -- ^ Extra names to consider
  , keep_all_names :: Bool
  -- ^ Keep unused names
  }
  deriving Show

commaSep :: [String] -> [String]
commaSep = concatMap (splitOn ",")

parseParams :: Parser Params
parseParams = Params
  <$> many (strOption (long "include" <> short 'i' <> metavar "PATH" <> help "Extra include directory"))
  <*> many (foldr (<|>) empty [ flag' debug_flag (long (flagifyShow debug_flag) <> help (debugHelp debug_flag))
                              | debug_flag <- [minBound..maxBound]
                              ])
  <*> (pure Nothing <|> fmap (Just . commaSep) (many (strOption prop_opt)))
  <*> fmap commaSep (many (strOption (long "extra" <> short 'e' <> metavar "NAME" <> help "Function declaration to add to theory")))
  <*> flag False True (long "keep-all-functions" <> help "Don't remove unused functions from the theory")
  where

  prop_opt = long "only" <> long "prop" <> short 'p' <> metavar "NAME" <> help "Property declaration to consider (default all)"

-- | Default (empty) parameters
defaultParams :: Params
defaultParams = Params
  { include = []
  , debug_flags = []
  , prop_names = Nothing
  , extra_names = []
  }

-- | Debugging flags
data DebugFlag = PrintCore | PrintInitialTheory
  deriving (Eq,Show,Enum,Bounded)

debugHelp :: DebugFlag -> String
debugHelp PrintCore          = "Print core bindings from GHC"
debugHelp PrintInitialTheory = "Print initial theory"
