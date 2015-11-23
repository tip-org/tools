{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ViewPatterns, ScopedTypeVariables #-}
module Tip.Pretty.Waldmeister where

import Text.PrettyPrint

import qualified Tip.Pretty.SMT as SMT

import Tip.Pretty
import Tip.Types
import Tip.Core
import Tip.Utils.Rename
import Tip.Utils
import Data.Generics.Geniplate
import Data.Maybe
import Data.Char (isAlphaNum,isDigit)
import Data.List (sortBy)
import Data.Ord (comparing)

import Control.Monad.State
import Control.Monad

validChar :: Char -> String
validChar x
  | isAlphaNum x                             = [x]
  | x `elem` ("~!@$%^&*_-+=<>.?/" :: String) = [x]
  | otherwise                                = ""

ppTheory :: (Ord a, PrettyVar a) => Theory a -> Doc
ppTheory
  (renameWithBlocks keywords
    (disambig (concatMap validChar . varStr))
      -> thy@Theory{..}) =
  vcat
    [ "NAME" <+> "tip"
    , "MODE" <+> if null gs then "COMPLETION" else "PROOF"
    , "SORTS" $\ vcat (map (ppVar . sort_name) thy_sorts)
    , "SIGNATURE" $\ vcat (map ppSig thy_sigs)
    , "ORDERING" $\
        vcat
          ["KBO",
           hsep (punctuate "," [ppVar (sig_name sig) <> "=1" | sig <- thy_sigs]),
           hsep (punctuate " >"
                (map (ppVar . sig_name)
                (reverse
                (sortBy (comparing (length . polytype_args . sig_type))
                        thy_sigs))))]
    , "VARIABLES" $\
        vcat [ ppVar x <+> ":" <+> ppType t
             | Local x t :: Local String <- usort (universeBi thy) ]
    , "EQUATIONS" $\ vcat (map ppFormula as)
    , "CONCLUSION" $\ vcat (map ppFormula gs)
    ]
  where
  (gs,as) = theoryGoals thy

ppType :: (Ord a, PrettyVar a) => Type a -> Doc
ppType (TyCon t []) = ppVar t
ppType t            = error $ "Waldmeister: cannot handle any sophisticated types: " ++ show (SMT.ppType t)

ppSig :: (Ord a,PrettyVar a) => Signature a -> Doc
ppSig (Signature f (PolyType [] arg_types res_type)) =
  hsep $ [ppVar f,":"] ++ map ppType arg_types ++ ["->",ppType res_type]

ppFormula :: (Ord a, PrettyVar a) => Formula a -> Doc
ppFormula = ppExpr . snd . forallView . fm_body

ppExpr :: (Ord a, PrettyVar a) => Expr a -> Doc
ppExpr (Builtin Equal :@: [e1,e2]) = hsep [ppExpr e1,"=",ppExpr e2]
ppExpr (hd :@: [])  = ppHead hd
ppExpr (hd :@: es)  = hcat ([ppHead hd <> "("] ++ punctuate "," (map ppExpr es)) <> ")"
ppExpr (Lcl l)      = ppVar (lcl_name l)
ppExpr Quant{}      = error "Waldmeister: cannot handle nested quantifiers"
ppExpr Lam{}        = error "Waldmeister: defunctionalize"
ppExpr Match{}      = error "Waldmeister: axiomatize funcdecls and lift matches"
ppExpr Let{}        = error "Waldmeister: lift let declarations"

ppHead :: (Ord a, PrettyVar a) => Head a -> Doc
ppHead (Gbl (Global g _ _)) = ppVar g
ppHead (Builtin (Lit (Bool b))) = text (show b)
ppHead (Builtin b)          = error $ "Waldmeister: cannot handle any builtins! Offending builtin:" ++ show b

keywords :: [String]
keywords = words "> -> : NAME MODE SORTS SIGNATURE ORDERING LPO KBO VARIABLES EQUATIONS CONCLUSION PROOF COMPLETION"
