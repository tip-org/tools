-- | Parses the TIP format
module Tip.Parser(parse,parseFile,Id,idPos) where

import Data.Monoid

import Tip.Parser.ParTIP
import Tip.Parser.AbsTIP (Start(..))
import Tip.Parser.ErrM

import Tip.Parser.Convert
import Tip.Core

-- | Parse from a file. If the string is empty or "-", then reads from stdin.
parseFile :: String -> IO (Either String (Theory Id))
parseFile file =
  do s <- case file of
       ""  -> getContents
       "-" -> getContents
       _   -> readFile file
     return (parse s)

-- | Parse, and get either an error or the string's theory
parse :: String -> Either String (Theory Id)
parse s =
  case pStart . myLexer $ s of
    Ok (Start ds) -> runCM (trDecls ds)
    Bad err       -> Left err

