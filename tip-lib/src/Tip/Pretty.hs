{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Tip.Pretty where

import Text.PrettyPrint

import Tip.Types

infixl 1 $\

-- | Typeclass for pretty things
class Pretty a where
  pp :: a -> Doc

-- | Pretty to string
ppRender :: Pretty a => a -> String
ppRender = render . pp

-- | Print something pretty
pprint :: Pretty a => a -> IO ()
pprint = putStrLn . ppRender

instance PrettyVar String where
  varStr = id

instance PrettyVar Int where
  varStr = show

-- | Typeclass for variables
class PrettyVar a where
  -- | The string in a variable
  varStr :: a -> String

instance (PrettyVar a,PrettyVar b) => PrettyVar (Either a b) where
  varStr (Left x)  = varStr x
  varStr (Right y) = varStr y

instance (Pretty a,Pretty b) => Pretty (a,b) where
  pp (x,y) = parens (pp x <+> "," $\ pp y)

instance (Pretty a,Pretty b,Pretty c) => Pretty (a,b,c) where
  pp (x,y,z) = parens (pp x <+> "," $\ pp y <+> "," $\ pp z)

instance (Pretty a) => Pretty [a] where
  pp xs = brackets (sep (punctuate "," (map pp xs)))

instance Pretty Int where
  pp = int

instance Pretty () where
  pp _ = "()"

newtype PPVar a = PPVar { unPPVar :: a }
  deriving (Eq,Ord,PrettyVar)

instance PrettyVar a => Pretty (PPVar a) where
  pp (PPVar x) = ppVar x

instance PrettyVar a => Show (PPVar a) where
  show (PPVar x) = varStr x

-- | Variable to 'Doc'
ppVar :: PrettyVar a => a -> Doc
ppVar = text . varStr

-- * Utilities on Docs

-- | Infix 'hang'
($\) :: Doc -> Doc -> Doc
d1 $\ d2 = hang d1 2 d2


-- | Conditional parentheses
parIf :: Bool -> Doc -> Doc
parIf True  = parens
parIf False = id

