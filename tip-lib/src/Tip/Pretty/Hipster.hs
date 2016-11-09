{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ScopedTypeVariables, ViewPatterns #-}
module Tip.Pretty.Hipster where

import Text.PrettyPrint

import Tip.Pretty
import Tip.Types
import Tip.Utils.Rename (renameWith,disambig)
import Tip.Rename
import Tip.Core (ifView, DeepPattern(..), patternMatchingView, topsort, makeGlobal, exprType)

import Data.Char
import Data.Maybe
import Data.List (intersperse, partition)

import Data.Generics.Geniplate

import qualified Data.Set as S


($-$), block :: Doc -> Doc -> Doc
d $-$ b = vcat [d,"",b]

block d c = (d $\ c)

pcsv, csv, csv1 :: [Doc] -> Doc
csv = fsep . punctuate ","

csv1 [x] = x
csv1 xs  = pcsv xs

pcsv = parens . csv

separating :: ([Doc] -> Doc) -> [Doc] -> [Doc] -> Doc
separating comb seps docs = comb (go seps docs)
  where
    go (s:ss) (d:ds) = s <+> d : go ss ds
    go _      []     = []
    go []     _      = error "separating: ran out of separators!"


intersperseWithPre :: (a -> a -> a) -> a -> [a] -> [a]
intersperseWithPre f  s (t1:t2:ts) = t1:map (f s) (t2:ts)
intersperseWithPre _f _s ts        = ts

quote :: Doc -> Doc
quote d = "\""<> d <> "\""

quoteWhen :: (a -> Bool) -> a -> (Doc -> Doc)
quoteWhen p t | p t       = quote
              | otherwise = id

ppAsTuple :: [a] -> (a -> Doc) -> Doc
ppAsTuple ts toDoc = parIf (length ts > 1) ((sep.punctuate ",") (map toDoc ts))

-- Pretty print the conjectues of this theory
ppHipsterConjs :: (Ord a, PrettyVar a) => Theory a -> Doc
ppHipsterConjs thy
  = foldl ($-$) empty
      (zipWith (ppHipsterFormula False) (thy_asserts thy) [0..])

ppQuant :: (PrettyVar a, Ord a) => Doc -> [Local a] -> Doc -> Doc -> Doc
ppQuant _name [] _to d = d
ppQuant name  ls to  d = (name $\ fsep (map (parens . ppLocalBinder) ls) <+> to) $\ d

ppBinder :: (PrettyVar a, Ord a) => a -> Type a -> Doc
ppBinder x t = ppVar x <+> "::" $\ ppType 0 t

ppLocalBinder :: (PrettyVar a, Ord a) => Local a -> Doc
ppLocalBinder (Local x t) = ppBinder x t

ppFuncs :: (PrettyVar a, Ord a) => [Function a] -> Doc
ppFuncs []       = empty
ppFuncs (fn:fns) = header <+>
    vcat (intersperseWithPre ($\) "and" fTys) <+> "where" $$
    vcat (intersperseWithPre ($\) "|" fDefs) $$
    termination
  where (header,termination) | null fns  = ("fun",empty)
                             | otherwise = ("function","by pat_completeness auto")
        (fTys, fDefs) = foldr (\(ppFunc -> (pf,pds)) (ftys,fdefs) ->
                                  (pf:ftys, pds++fdefs))
                        ([],[]) (fn:fns)

ppFunc :: (PrettyVar a, Ord a) => Function a -> (Doc,[Doc])
ppFunc (Function f _tvs xts t e) =
     (ppVar f <+> "::" <+> quote (ppType (-1) (map lcl_type xts :=>: t)),
      [ quote $ ppVar f $\ fsep (map ppDeepPattern dps) <+> "=" $\ ppExpr 0 rhs
                  | (dps,rhs) <- patternMatchingView xts e ])


ppDeepPattern :: PrettyVar a => DeepPattern a -> Doc
ppDeepPattern (DeepConPat (Global k _ _) dps) = parens (ppVar k <+> fsep (map ppDeepPattern dps))
ppDeepPattern (DeepVarPat (Local x _)) = ppVar x
ppDeepPattern (DeepLitPat lit) = ppLit lit


ppHipsterFormula :: (PrettyVar a, Ord a) => Bool -> Formula a -> Int -> Doc
ppHipsterFormula explicit_forall (Formula role _ _tvs term)  i =
  ppExprStripTopForall explicit_forall 0 term

-- Maybe strip away explicit top-level forall quantifiers.
ppExprStripTopForall :: (PrettyVar a, Ord a) => Bool -> Int -> Expr a -> Doc
ppExprStripTopForall False i (Quant _ Forall ls e) = ppExprStripTopForall False i e
ppExprStripTopForall _ i term = ppExpr i term

ppExpr :: (PrettyVar a, Ord a) => Int -> Expr a -> Doc
ppExpr i e | Just (c,t,f) <- ifView e = parens $ "if" $\ ppExpr 0 c $\ "then" $\ ppExpr 0 t $\ "else" $\ ppExpr 0 f
ppExpr i e@(hd@(Gbl Global{..}) :@: es)
  | isNothing (makeGlobal gbl_name gbl_type (map exprType es) Nothing) =
    parIf (i > 0) $
    ppHead hd (map (ppExpr 1) es)-- -- $\ "::" $\ ppType 0 (exprType e)
ppExpr i (hd :@: es)  = parIf ((i > 0 && not (null es)) || isLogB hd) $
                          ppHead hd (map (ppExpr 1) es)
  where isLogB (Builtin b) = logicalBuiltin b
        isLogB _           = False
ppExpr _ (Lcl l)      = parens (ppVar (lcl_name l) <+> "::" <+> (ppType 0 (lcl_type l)))
ppExpr i (Lam ls e)   = parIf (i > 0) $ ppQuant "%" ls "=>" (ppExpr 0 e)
ppExpr i (Let x b e)  = parIf (i > 0) $ sep ["let" $\ ppLocalBinder x <+> "=" $\ ppExpr 0 b, "in" <+> ppExpr 0 e]
ppExpr i (Quant _ q ls e) = parIf (i > 0) $ ppQuant (ppQuantName q) ls "." (ppExpr 0 e)
ppExpr i (Match e alts) =
  parIf (i <= 0) $ block ("case" $\ ppExpr 0 e $\ "of")
                         (vcat (intersperseWithPre ($\) "|" (map ppCase
                                  (uncurry (++) (partition ((/= Default).case_pat) alts)))))

ppHead :: (PrettyVar a, Ord a) => Head a -> [Doc] -> Doc
ppHead (Gbl gbl)      args                        = renameHipsterFuns (gbl_name gbl) $\ fsep args
ppHead (Builtin b)    [u,v] | Just d <- ppBinOp b = u <+> d $\ v
ppHead (Builtin At{}) args                        = fsep args
ppHead (Builtin b)    args                        = ppBuiltin b $\ fsep args

-- Rename functions back to Isabelle-names for use in Hipster.
renameHipsterFuns :: (PrettyVar a, Ord a) => a -> Doc
renameHipsterFuns gbl_fun =
  case fun_name of
      "Zero_nat" -> "Groups.zero_class.zero"
      "one_nat" -> "Groups.one_class.one"
      "plus_nat" -> "Groups.plus_class.plus"
      "++" -> "List.append"
      "reverse" -> "List.rev"
      otherwise -> fun_name
  where fun_name = ppVar gbl_fun

ppBuiltin :: Builtin -> Doc
ppBuiltin (Lit lit) = ppLit lit
ppBuiltin IntDiv    = "(op div)"
ppBuiltin IntMod    = "mod"
ppBuiltin Not       = "~"
ppBuiltin NumWiden  = "of_int"
ppBuiltin b         = error $ "Isabelle.ppBuiltin: " ++ show b

ppBinOp :: Builtin -> Maybe Doc
ppBinOp And       = Just "&"
ppBinOp Or        = Just "|"
ppBinOp Implies   = Just "==>"
ppBinOp Equal     = Just "="
ppBinOp Distinct  = Just "~="
ppBinOp NumAdd    = Just "+"
ppBinOp NumSub    = Just "-"
ppBinOp NumMul    = Just "*"
ppBinOp NumDiv    = Just "/"
ppBinOp NumGt     = Just ">"
ppBinOp NumGe     = Just ">="
ppBinOp NumLt     = Just "<"
ppBinOp NumLe     = Just "<="
ppBinOp _         = Nothing

ppLit :: Lit -> Doc
ppLit (Int i)      = integer i
ppLit (Bool True)  = "True"
ppLit (Bool False) = "False"
ppLit (String s)   = text (show s)

ppQuantName :: Quant -> Doc
ppQuantName Forall = "!"
ppQuantName Exists = "?"

ppCase :: (PrettyVar a, Ord a) => Case a -> Doc
ppCase (Case pat rhs) = ppPat pat <+> "=>" $\ ppExpr 0 rhs

ppPat :: (PrettyVar a, Ord a) => Pattern a -> Doc
ppPat pat = case pat of
  Default     -> "other"
  ConPat g ls -> ppVar (gbl_name g) $\ fsep (map (ppVar . lcl_name) ls)
  LitPat l    -> ppLit l

ppType :: (PrettyVar a, Ord a) => Int -> Type a -> Doc
ppType _ (TyVar x)     = ppTyVar x
ppType i (TyCon tc ts) = parIf (i > 0 && (not . null) ts) $
                           ppAsTuple ts (ppType 2) $\ ppHipsterType tc
ppType i (ts :=>: r)   = parIf (i >= 0) $ fsep (punctuate " =>" (map (ppType 0) (ts ++ [r])))
ppType _ (BuiltinType Integer) = "integer"
ppType _ (BuiltinType Real)    = "real"
ppType _ (BuiltinType Boolean) = "bool"

ppTyVar :: (PrettyVar a, Ord a) => a -> Doc
ppTyVar x = "'" <> ppVar x

-- Rename back to Isabelle built in type names when needed.
ppHipsterType :: (PrettyVar a, Ord a) => a -> Doc
ppHipsterType tc =
  case type_name of
      "Nat" -> "nat"
      otherwise -> type_name
  where type_name = ppVar tc
