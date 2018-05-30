{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ScopedTypeVariables, ViewPatterns #-}
module Tip.Pretty.Hopster(ppHopsterConjs) where

import Text.PrettyPrint

import Tip.Pretty
import Tip.Types
import Tip.Core (ifView, makeGlobal, exprType, free, source, getAttr, getAttrs, hasAttr, unitAttr)
import Tip.Scope

import Data.Maybe
import Data.List (partition, intersect)

($-$), block :: Doc -> Doc -> Doc
d $-$ b = vcat [d,"",b]

block d c = (d $\ c)

intersperseWithPre :: (a -> a -> a) -> a -> [a] -> [a]
intersperseWithPre f  s (t1:t2:ts) = t1:map (f s) (t2:ts)
intersperseWithPre _f _s ts        = ts

ppAsTuple :: [a] -> (a -> Doc) -> Doc
ppAsTuple ts toDoc = parIf (length ts > 1) ((sep.punctuate ",") (map toDoc ts))

-- Pretty print the conjectues of this theory
ppHopsterConjs :: (Ord a, PrettyVar a) => Theory a -> Doc
ppHopsterConjs thy
  = foldl ($-$) empty
      (zipWith (ppHopsterFormula (scope thy)) (thy_asserts thy) [0..])

ppHopsterFormula :: (PrettyVar a, Ord a) => Scope a -> Formula a -> Int -> Doc
ppHopsterFormula scp Formula{..}  i =
  ppExprStripTopForall scp 0 fm_body

ppQuant :: (PrettyVar a, Ord a) => Scope a -> Doc -> [Local a] -> Doc -> Doc -> Doc
ppQuant _scp _name [] _to d = d
ppQuant scp name  ls to  d = (name $\ fsep (map (parens . ppLocalBinder scp) ls) <+> to) $\ d

ppBinder :: (PrettyVar a, Ord a) => Scope a -> a -> Type a -> Doc
ppBinder scp x t = ppVar x <+> ":" $\ ppType scp 0 t

ppLocalBinder :: (PrettyVar a, Ord a) => Scope a -> Local a -> Doc
ppLocalBinder scp (Local x t) = ppBinder scp x t

-- Maybe strip away explicit top-level forall quantifiers.
ppExprStripTopForall :: (PrettyVar a, Ord a) => Scope a -> Int -> Expr a -> Doc
ppExprStripTopForall scp i (Quant _ Forall ls e) = ppExprStripTopForall scp i e
ppExprStripTopForall scp i term = ppExpr scp i term

ppExpr :: (PrettyVar a, Ord a) => Scope a -> Int -> Expr a -> Doc
ppExpr scp i e | Just (c,t,f) <- ifView e = parens $ "if" $\ ppExpr scp 0 c $\ "then" $\ ppExpr scp 0 t $\ "else" $\ ppExpr scp 0 f
ppExpr scp i e@(hd@(Gbl Global{..}) :@: es)
  | isNothing (makeGlobal gbl_name gbl_type (map exprType es) Nothing) =
    parIf (i > 0) $
    ppHead scp hd (map (ppExpr scp 1) es)-- -- $\ ":" $\ ppType 0 (exprType e)
ppExpr scp i (hd :@: es)  = parIf ((i > 0 && not (null es)) || isLogB hd) $
                            ppHead scp hd (map (ppExpr scp 1) es)
  where isLogB (Builtin b) = logicalBuiltin b
        isLogB _           = False
ppExpr scp _ (Lcl l)      = parens (ppVar (lcl_name l) <+> ":" <+> (ppType scp 0 (lcl_type l)))
ppExpr scp i (Lam ls (gbl :@: args))
  -- Eta-reduction for terms of the form:
  -- \x1...xn. f(t1...tm, x1...xn)
  | (args1, args2) <- splitAt (length args - length ls) args,
    args2 == map Lcl ls,
    ls `intersect` concatMap free args1 == [] =
    ppExpr scp i (gbl :@: args1)
ppExpr scp i (Lam ls e)   = parIf (i > 0) $ ppQuant scp "\\" ls "." (ppExpr scp 0 e)
ppExpr scp i (Let x b e)  = parIf (i > 0) $ sep ["let" $\ ppLocalBinder scp x <+> "=" $\ ppExpr scp 0 b, "in" <+> ppExpr scp 0 e]
ppExpr scp i (Quant _ q ls e) = parIf (i > 0) $ ppQuant scp (ppQuantName q) ls "." (ppExpr scp 0 e)
ppExpr scp i (Match e alts) =
  parIf (i <= 0) $ block ("case" $\ ppExpr scp 0 e $\ "of")
                         (vcat (intersperseWithPre ($\) "|" (map (ppCase scp)
                                  (uncurry (++) (partition ((/= Default).case_pat) alts)))))
ppExpr _ _ LetRec{} = error "letrec not supported"

ppHead :: (PrettyVar a, Ord a) => Scope a -> Head a -> [Doc] -> Doc
ppHead scp (Gbl gbl) args | fromMaybe False (hasAttr (unitAttr "tuple") <$> getAttrs <$> lookupGlobal (gbl_name gbl) scp) =
  sep (punctuate "," args)
ppHead scp (Gbl gbl) args = ppVar (gbl_name gbl) $\ fsep args
ppHead _ (Builtin b)    [u,v] | Just d <- ppBinOp b = u <+> d $\ v
ppHead _ (Builtin At{}) args                        = fsep args
ppHead _ (Builtin b)    args                        = ppBuiltin b $\ fsep args

ppBuiltin :: Builtin -> Doc
ppBuiltin (Lit lit) = ppLit lit
ppBuiltin IntDiv    = "DIV"
ppBuiltin IntMod    = "MOD"
ppBuiltin Not       = "~"
ppBuiltin NumWiden  = ""
ppBuiltin b         = error $ "Hopster.ppBuiltin: " ++ show b

ppBinOp :: Builtin -> Maybe Doc
ppBinOp And       = Just "/\\"
ppBinOp Or        = Just "\\/"
ppBinOp Implies   = Just "==>"
ppBinOp Equal     = Just "="
ppBinOp Distinct  = Just "<>"
ppBinOp NumAdd    = Just "+"
ppBinOp NumSub    = Just "-"
ppBinOp NumMul    = Just "*"
ppBinOp NumDiv    = Just "DIV"
ppBinOp NumGt     = Just ">"
ppBinOp NumGe     = Just ">="
ppBinOp NumLt     = Just "<"
ppBinOp NumLe     = Just "<="
ppBinOp _         = Nothing

ppLit :: Lit -> Doc
ppLit (Int i)      = integer i
ppLit (Bool True)  = "T"
ppLit (Bool False) = "F"

ppQuantName :: Quant -> Doc
ppQuantName Forall = "!"
ppQuantName Exists = "?"

ppCase :: (PrettyVar a, Ord a) => Scope a -> Case a -> Doc
ppCase scp (Case pat rhs) = ppPat pat <+> "=>" $\ ppExpr scp 0 rhs

ppPat :: (PrettyVar a, Ord a) => Pattern a -> Doc
ppPat pat = case pat of
  Default     -> "other"
  ConPat g ls -> ppVar (gbl_name g) $\ fsep (map (ppVar . lcl_name) ls)
  LitPat l    -> ppLit l

ppType :: (PrettyVar a, Ord a) => Scope a -> Int -> Type a -> Doc
ppType _ _ (TyVar x)     = ppTyVar x
-- XXX scope
ppType scp i (TyCon tc ts) | fromMaybe False (hasAttr (unitAttr "tuple") <$> getAttrs <$> lookupType tc scp)
                           = parIf (i > 0) $
                             ((sep.punctuate " #") (map (ppType scp 0) ts))
                              -- ppAsTuple ts (ppType 2) $\ ppHopsterType tc
ppType scp i (TyCon tc ts) = parIf (i > 0 && (not . null) ts) $
                             ppAsTuple ts (ppType scp 2) $\ ppVar tc
ppType scp i (ts :=>: r)   = parIf (i >= 0) $ fsep (punctuate " ->" (map (ppType scp 0) (ts ++ [r])))
ppType _ _ (BuiltinType Integer) = "num"
ppType _ _ (BuiltinType Real)    = "num"
ppType _ _ (BuiltinType Boolean) = "bool"

ppTyVar :: (PrettyVar a, Ord a) => a -> Doc
ppTyVar x = "'" <> ppVar x
