module Tip.Params where

-- | Parameters
data Params = Params
  { file        :: FilePath
  -- ^ File to process
  , include     :: [FilePath]
  -- ^ Directories to include
  , flags       :: [DebugFlags]
  -- ^ Debugging flags
  , only        :: [String]
  -- ^ Only consider these properties
  , extra       :: [String]
  -- ^ Also translate these functions and its transitive dependencies
  }
  deriving Show

-- | Default parameters, given the name of the file to process
defaultParams :: FilePath -> Params
defaultParams fp = Params
  { file = fp
  , include = []
  , flags = []
  , only = []
  , extra = []
  }

-- | Debugging flags
data DebugFlags = PrintCore | PrintProps | PrintExtraIds | PrintInitialTip
  deriving (Eq,Show)

