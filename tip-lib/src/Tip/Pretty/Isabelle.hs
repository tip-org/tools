{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ScopedTypeVariables, ViewPatterns #-}
module Tip.Pretty.Isabelle where

import Text.PrettyPrint

import Tip.Pretty
import Tip.Types
import Tip.Utils.Renamer (renameWith,disambig)
import Tip.Renamer
import Tip (ifView, DeepPattern(..), patternMatchingView, topsort, makeGlobal, exprType)

import Data.Char
import Data.Maybe
import Data.List (intersperse)

import Data.Generics.Geniplate

import qualified Data.Set as S


{-
data Why3Var a = Why3Var Bool {- is constructor -} a
  deriving (Eq,Ord,Show)

instance PrettyVar a => PrettyVar (Why3Var a) where
  varStr (Why3Var b x) = (if b then toUpper else toLower) `mapHead` addAlpha (varStr x)
   where
    mapHead :: (Char -> Char) -> String -> String
    f `mapHead` []     = [f 'x']
    f `mapHead` (x:xs) = f x:xs

    addAlpha :: String -> String
    addAlpha s@(x:_) | isAlpha x = s
    addAlpha s                   = "x" ++ s

why3VarTheory :: forall a . Ord a => Theory a -> Theory (Why3Var a)
why3VarTheory thy = fmap mk thy
 where
  cons = S.fromList [ c | Constructor c _ _ <- universeBi thy ]
  mk x = Why3Var (x `S.member` cons) x
-}

block :: Doc -> Doc -> Doc
block d c = (d $\ c) $$ "end"

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

escape :: Char -> String
escape x | isAlphaNum x = [x]
escape _                = []

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

($-$) :: Doc -> Doc -> Doc
d $-$ b = vcat [d,"",b]--d <> ("\n" $$ b)

ppTheory :: (Ord a, PrettyVar a) => Theory a -> Doc
ppTheory (renameAvoiding isabelleKeywords escape -> Theory{..})
  = vcat ["theory" <+> "A",  
          --"imports $HIPSTER_HOME/IsaHipster",
          "imports Main",
          "        \"../../IsaHipster\"",
          "begin"] $$
    foldl ($-$) empty (
      map ppSort thy_sorts ++
      map ppDatas (topsort thy_datatypes) ++
      map ppUninterp thy_sigs ++
      map ppFuncs (topsort thy_funcs) ++
      ["(*hipster" <+> sep (map (ppVar.func_name) thy_funcs) <+> "*)"] ++
      zipWith ppFormula thy_asserts [0..])
    $-$
    "end"

ppSort :: (PrettyVar a, Ord a) => Sort a -> Doc
--ppSort (Sort sort 0) = "type" $\ ppVar sort
ppSort (Sort sort n) =
  error $ "Can't translate abstract sort " ++ show (ppVar sort) ++ " of arity " ++ show n ++ " to Isabelle"

ppDatas :: (PrettyVar a, Ord a) => [Datatype a] -> Doc
ppDatas [d] = ppData "datatype" d-- vcat (ppData "datatype" d:map (ppData "and") ds)

ppData :: (PrettyVar a, Ord a) => Doc -> Datatype a -> Doc
ppData header (Datatype tc tvs cons) =
  header $\ ppAsTuple tvs ppTyVar $\
    ppVar tc $\ separating fsep ("=":repeat "|") (map ppCon cons)
--ppDatas (d:ds) = ppData "datatype" d
        -- FIXME: No mutual recusion for now... 
        --vcat (ppData "type" d:map (ppData "with") ds)

ppCon :: (PrettyVar a, Ord a) => Constructor a -> Doc
ppCon (Constructor c _d as) = ppVar c <+> fsep (map (quote . ppType 0 . snd) as)

ppQuant :: (PrettyVar a, Ord a) => Doc -> [Local a] -> Doc -> Doc -> Doc
ppQuant _name [] _to d = d
ppQuant name  ls to  d = (name $\ fsep (map (parens . ppLocalBinder) ls) <+> to) $\ d

ppBinder :: (PrettyVar a, Ord a) => a -> Type a -> Doc
ppBinder x t = ppVar x <+> "::" $\ ppType 0 t

ppLocalBinder :: (PrettyVar a, Ord a) => Local a -> Doc
ppLocalBinder (Local x t) = ppBinder x t

ppUninterp :: (PrettyVar a, Ord a) => Signature a -> Doc
ppUninterp (Signature f (PolyType _ arg_types result_type)) =
  --"function" $\ ppVar f $\ fsep (map (ppType 1) arg_types) $\ (":" <+> ppType 1 result_type)
  error $ "Can't translate uninterpreted function " ++ varStr f

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

   -- (header $\ ppVar f $\ fsep (map (parens . ppLocalBinder) xts) $\ (":" <+> ppType 0 t <+> "="))
   --  $\ ppExpr 0 e

ppDeepPattern :: PrettyVar a => DeepPattern a -> Doc
ppDeepPattern (DeepConPat (Global k _ _) dps) = parens (ppVar k <+> fsep (map ppDeepPattern dps))
ppDeepPattern (DeepVarPat (Local x _)) = ppVar x
ppDeepPattern (DeepLitPat lit) = ppLit lit


ppFormula :: (PrettyVar a, Ord a) => Formula a -> Int -> Doc
ppFormula (Formula role _tvs term) i =
  (ppRole role <+> ("x" <> int i) <+> ":") $\ quote (ppExpr 0 term) $$
  "by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})"

ppRole :: Role -> Doc
ppRole Assert = "lemma" --Better with lemma and sorry-proof here. Then need to insert 'sorry' on the line below somehow.
ppRole Prove  = "theorem"

ppExpr :: (PrettyVar a, Ord a) => Int -> Expr a -> Doc
ppExpr i e | Just (c,t,f) <- ifView e = parens $ "if" $\ ppExpr 0 c $\ "then" $\ ppExpr 0 t $\ "else" $\ ppExpr 0 f
ppExpr i e@(hd@(Gbl Global{..}) :@: es)
  | isNothing (makeGlobal gbl_name gbl_type (map exprType es) Nothing) =
    parIf (i > 0) $
    ppHead hd (map (ppExpr 1) es)-- $\ "::" $\ ppType 0 (exprType e)
ppExpr i (hd :@: es)  = parIf (i > 0 && not (null es)) $ ppHead hd (map (ppExpr 1) es)
ppExpr _ (Lcl l)      = ppVar (lcl_name l)
ppExpr i (Lam ls e)   = parIf (i > 0) $ ppQuant "%" ls "=>" (ppExpr 0 e)
ppExpr i (Let x b e)  = parIf (i > 0) $ sep ["let" $\ ppLocalBinder x <+> "=" $\ ppExpr 0 b, "in" <+> ppExpr 0 e]
ppExpr i (Quant _ q ls e) = parIf (i > 0) $ ppQuant (ppQuantName q) ls "." (ppExpr 0 e)
ppExpr i (Match e alts) =
  parIf (i > 0) $ block ("case" $\ ppExpr 0 e $\ "of")
                        (separating vcat (repeat "|") (map ppCase alts))

ppHead :: (PrettyVar a, Ord a) => Head a -> [Doc] -> Doc
ppHead (Gbl gbl)      args                        = ppVar (gbl_name gbl) $\ fsep args
ppHead (Builtin b)    [u,v] | Just d <- ppBinOp b = u <+> d $\ v
ppHead (Builtin At{}) args                        = fsep args
ppHead (Builtin b)    args                        = ppBuiltin b $\ fsep args

ppBuiltin :: Builtin -> Doc
ppBuiltin (Lit lit) = ppLit lit
ppBuiltin IntDiv    = "div"
ppBuiltin IntMod    = "mod"
ppBuiltin Not       = "~"
ppBuiltin b         = error $ "Isabelle.ppBuiltin: " ++ show b

ppBinOp :: Builtin -> Maybe Doc
ppBinOp And       = Just "&"
ppBinOp Or        = Just "|"
ppBinOp Implies   = Just "==>"
ppBinOp Equal     = Just "="
ppBinOp Distinct  = Just "~="
ppBinOp IntAdd    = Just "+"
ppBinOp IntSub    = Just "-"
ppBinOp IntMul    = Just "*"
ppBinOp IntGt     = Just ">"
ppBinOp IntGe     = Just ">="
ppBinOp IntLt     = Just "<"
ppBinOp IntLe     = Just "<="
ppBinOp _         = Nothing

ppLit :: Lit -> Doc
ppLit (Int i)      = integer i
ppLit (Bool True)  = "True"
ppLit (Bool False) = "False"
ppLit (String s)   = text (show s)

ppQuantName :: Quant -> Doc
ppQuantName Forall = "!!"
ppQuantName Exists = "??"

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
                           ppAsTuple ts (ppType 2) {-fsep (map (ppType 2 {-1-}) ts)-} $\ ppVar tc
ppType i (ts :=>: r)   = parIf (i >= 0) $ fsep (punctuate " =>" (map (ppType 0) (ts ++ [r])))
ppType _ (BuiltinType Integer) = "int"
ppType _ (BuiltinType Boolean) = "bool"

ppTyVar :: (PrettyVar a, Ord a) => a -> Doc
ppTyVar x = "'" <> ppVar x

-- FIXME: THESE are just copied from the Why3-file
isabelleKeywords :: [String]
isabelleKeywords = (words . unlines)
    [ "equal not use import goal int"
    , "and or"
    , "forall exists"
    , "module theory"
    , "ac"
    , "and"
    , "axiom"
    , "inversion"
    , "bitv"
    , "check"
    , "cut"
    , "distinct"
    , "else"
    , "exists"
    , "false"
    , "forall"
    , "function"
    , "goal"
    , "if"
    , "in"
    , "include"
    , "int"
    , "let"
    , "logic"
    , "not"
    , "or"
    , "predicate"
    , "prop"
    , "real"
    , "rewriting"
    , "then"
    , "true"
    , "type"
    , "unit"
    , "void"
    , "with"
    , "sign Nil Cons"
    , "div"
    , "mod"
    ] ++
    [ "theorem lemma axiom declare axiomatization"
    , "prefer def thm term typ"
    , "fun primrec definition value where infixl infixr abbreviation notation for"
    , "datatype type_synonym option consts typedecl inductive_set inductive_cases"
    , "True False None Some abs"
    , "class instantiation fixes instance assumes shows proof fix show have obtain"
    , "unfolding qed from"
    , "begin end imports ML using"
    , "apply done oops sorry by back"
    , "text header chapter section subsection subsubsection sect subsect subsubsect"
    , "nil cons Nil Cons"
    , "nil"
    , "cons"
    , "Nil"
    , "Cons"
    ]

