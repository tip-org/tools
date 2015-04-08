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

parIf :: Bool -> Doc -> Doc
parIf True  = parens
parIf False = id

class Pretty a where
  pp :: a -> Doc

instance PrettyVar Int where
  varStr = show

class PrettyVar a where
  varStr :: a -> String

ppVar :: PrettyVar a => a -> Doc
ppVar = text . varStr

