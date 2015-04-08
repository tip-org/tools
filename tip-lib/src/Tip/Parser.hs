module Tip.Parser where

import Data.Monoid

import Tip.Parser.ParTIP
import Tip.Parser.AbsTIP (Start(..))
import Tip.Parser.ErrM

import Tip.Parser.Convert
import Tip

parse :: String -> Either String (Theory Id)
parse s =
  case pStart . myLexer $ s of
    Ok (Start ds) -> runCM (trDecls ds)
    Bad err       -> Left err

