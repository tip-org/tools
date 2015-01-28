module Tip.Params where

data DebugFlags = PrintCore | PrintExtraIds
  deriving (Eq,Show)

-- | Parameters
data Params = Params
  { file        :: FilePath
  , include     :: [FilePath]
  , flags       :: [DebugFlags]
  , only        :: [String]
  , extra       :: [String]
  , extra_trans :: [String]
  }
  deriving Show

