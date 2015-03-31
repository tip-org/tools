{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
module Tip.Pretty where

import Text.PrettyPrint

import Tip.Types

infixl 1 $\

($\) :: Doc -> Doc -> Doc
d1 $\ d2 = hang d1 2 d2

ppRender :: Pretty a => a -> String
ppRender = render . pp

pprint :: Pretty a => a -> IO ()
pprint = putStrLn . ppRender

class Show a => Pretty a where
  pp :: a -> Doc

instance Pretty Int where
  pp = int

