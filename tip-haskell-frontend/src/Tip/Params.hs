module Tip.Params where

data DebugFlags = PrintCore | PrintProps | PrintExtraIds | PrintInitialTip
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

