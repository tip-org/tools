{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ViewPatterns #-}
module Tip.Pretty.SMT where

import Text.PrettyPrint

import Tip.Pretty
import Tip.Types
import Tip (ifView, topsort, neg, exprType, makeGlobal)
import Tip.Renamer
import Data.Maybe
import Data.Char (isAlphaNum)

expr,parExpr,parExprSep :: Doc -> [Doc] -> Doc
parExpr s [] = parens s
parExpr s xs = ("(" <> s) $\ (fsep xs <> ")")

parExprSep s [x]    = sep ["(" <> s,x <> ")"]
parExprSep s (x:xs) = sep ["(" <> s,x] $\ (fsep xs <> ")")
parExprSep s xs     = parExpr s xs

expr s [] = s
expr s xs = parExpr s xs

exprSep s [] = s
exprSep s xs = parExprSep s xs

apply :: Doc -> Doc -> Doc
apply s x = parExpr s [x]

validSMTChar :: Char -> String
validSMTChar x
  | isAlphaNum x                             = [x]
  | x `elem` ("~!@$%^&*_-+=<>.?/" :: String) = [x]
  | otherwise                                = ""

ppTheory :: (Ord a,PrettyVar a) => Theory a -> Doc
ppTheory (renameAvoiding smtKeywords validSMTChar -> Theory{..})
  = vcat
     (map ppSort thy_abs_type_decls ++
      map ppDatas (topsort thy_data_decls) ++
      map ppUninterp thy_abs_func_decls ++
      map ppFuncs (topsort thy_func_decls) ++
      map ppFormula thy_form_decls ++
      ["(check-sat)"])

ppSort :: PrettyVar a => AbsType a -> Doc
ppSort (AbsType sort n) = parExpr "declare-sort" [ppVar sort, int n]

ppDatas :: PrettyVar a => [Datatype a] -> Doc
ppDatas datatypes@(Datatype _ tyvars _:_) =
  parExprSep "declare-datatypes" [parens (fsep (map ppVar tyvars)), parens (fsep (map ppData datatypes))]

ppData :: PrettyVar a => Datatype a -> Doc
ppData (Datatype tycon _ datacons) =
  parExprSep (ppVar tycon) (map ppCon datacons)

ppCon :: PrettyVar a => Constructor a -> Doc
ppCon (Constructor datacon selector args) =
  parExprSep (ppVar datacon) [apply (ppVar p) (ppType t) | (p,t) <- args]


par :: (PrettyVar a) => [a] -> Doc -> Doc
par [] d = d
par xs d = parExprSep "par" [parens (fsep (map ppVar xs)), parens d]

par' :: (PrettyVar a) => [a] -> Doc -> Doc
par' [] d = d
par' xs d = parExprSep "par" [parens (fsep (map ppVar xs)), d]

ppUninterp :: PrettyVar a => AbsFunc a -> Doc
ppUninterp (AbsFunc f (PolyType tyvars arg_types result_type)) =
  apply "declare-fun"
    (par' tyvars
      (apply (ppVar f)
        (sep [parens (fsep (map ppType arg_types)), ppType result_type])))

ppFuncs :: (Ord a, PrettyVar a) => [Function a] -> Doc
ppFuncs fs = expr "define-funs-rec"
  [ parens (vcat (map ppFuncSig fs))
  , parens (vcat (map (ppExpr . func_body) fs))
  ]

ppFuncSig :: PrettyVar a => Function a -> Doc
ppFuncSig (Function f tyvars args res_ty body) =
  (par' tyvars
    (parens
      (ppVar f $\ fsep [ppLocals args, ppType res_ty])))

ppFormula :: (Ord a, PrettyVar a) => Formula a -> Doc
ppFormula (Formula Prove tvs term)  = apply "assert-not" (par' tvs (ppExpr term))
ppFormula (Formula Assert tvs term) = apply "assert"     (par' tvs (ppExpr term))

ppExpr :: (Ord a, PrettyVar a) => Expr a -> Doc
ppExpr e | Just (c,t,f) <- ifView e = parExpr "ite" (map ppExpr [c,t,f])
ppExpr e@(hd@(Gbl Global{..}) :@: es)
  | isNothing (makeGlobal gbl_name gbl_type (map exprType es) Nothing)
      = exprSep "as" [exprSep (ppHead hd) (map ppExpr es), ppType (exprType e)]
ppExpr (hd :@: es)  = exprSep (ppHead hd) (map ppExpr es)
ppExpr (Lcl l)      = ppVar (lcl_name l)
ppExpr (Lam ls e)   = parExprSep "lambda" [ppLocals ls,ppExpr e]
ppExpr (Match e as) = "(match" $\ ppExpr e $\ (vcat (map ppCase as) <> ")")
ppExpr (Let x b e)  = parExprSep "let" [parens (ppLocal x $\ ppExpr b), ppExpr e]
ppExpr (Quant _ q ls e) = parExprSep (ppQuant q) [ppLocals ls, ppExpr e]

ppLocals :: PrettyVar a => [Local a] -> Doc
ppLocals ls = parens (fsep (map ppLocal ls))

ppLocal :: PrettyVar a => Local a -> Doc
ppLocal (Local l t) = expr (ppVar l) [ppType t]

ppHead :: PrettyVar a => Head a -> Doc
ppHead (Builtin b) = ppBuiltin b
ppHead (Gbl gbl)   = ppVar (gbl_name gbl) -- $$ ";" <> ppPolyType (gbl_type gbl)
                                          -- $$ ";" <> fsep (map ppType (gbl_args gbl))
                                          -- $$ text ""

ppBuiltin :: Builtin -> Doc
ppBuiltin (Lit lit) = ppLit lit
ppBuiltin Not       = "not"
ppBuiltin And       = "and"
ppBuiltin Or        = "or"
ppBuiltin Implies   = "=>"
ppBuiltin Equal     = "="
ppBuiltin Distinct  = "distinct"
ppBuiltin IntAdd    = "+"
ppBuiltin IntSub    = "-"
ppBuiltin IntMul    = "*"
ppBuiltin IntGt     = ">"
ppBuiltin IntGe     = ">="
ppBuiltin IntLt     = "<"
ppBuiltin IntLe     = "<="
ppBuiltin At{}      = "@"

ppLit :: Lit -> Doc
ppLit (Int i)      = integer i
ppLit (Bool True)  = "true"
ppLit (Bool False) = "false"
ppLit (String s)   = text (show s)

ppQuant :: Quant -> Doc
ppQuant Forall = "forall"
ppQuant Exists = "exists"

ppCase :: (Ord a, PrettyVar a) => Case a -> Doc
ppCase (Case pat rhs) = parExprSep "case" [ppPat pat,ppExpr rhs]

ppPat :: PrettyVar a => Pattern a -> Doc
ppPat Default         = "default"
ppPat (ConPat g args) = expr (ppVar (gbl_name g)) [ppVar (lcl_name arg) | arg <- args]
ppPat (LitPat lit)    = ppLit lit

ppType :: PrettyVar a => Type a -> Doc
ppType (TyVar x)     = ppVar x
ppType (TyCon tc ts) = expr (ppVar tc) (map ppType ts)
ppType (ts :=>: r)   = parExpr "=>" (map ppType (ts ++ [r]))
ppType NoType        = "_"
ppType (BuiltinType Integer) = "int"
ppType (BuiltinType Boolean) = "bool"

-- Temporary use SMTLIB as the pretty printer:

instance (Ord a,PrettyVar a) => Pretty (Theory a) where
  pp = ppTheory

instance (Ord a, PrettyVar a) => Pretty (Expr a) where
  pp = ppExpr

ppPolyType :: PrettyVar a => PolyType a -> Doc
ppPolyType (PolyType tyvars arg_types result_type) =
  par tyvars
    (parens
      (sep [parens (fsep (map ppType arg_types)), ppType result_type]))

instance PrettyVar a => Pretty (PolyType a) where
  pp = ppPolyType

instance PrettyVar a => Pretty (Type a) where
  pp = ppType

instance (Ord a, PrettyVar a) => Pretty (Function a) where
  pp = ppFuncs . return

instance (Ord a, PrettyVar a) => Pretty (Formula a) where
  pp = ppFormula

instance PrettyVar a => Pretty (Datatype a) where
  pp = ppDatas . return

instance PrettyVar a => Pretty (AbsFunc a) where
  pp = ppUninterp

instance PrettyVar a => Pretty (Local a) where
  pp = ppLocal

instance PrettyVar a => Pretty (Global a) where
  pp = ppHead . Gbl

instance PrettyVar a => Pretty (Head a) where
  pp = ppHead

smtKeywords :: [String]
smtKeywords =
    [ "ac"
    , "and"
    , "axiom"
    , "inversion"
    , "bitv"
    , "bool"
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
    , "assert", "check-sat"
    , "abs", "min", "max", "const"
    , "=", "=>", "+", "-", "*", ">", ">=", "<", "<=", "@", "!"
    -- Z3:
    , "Bool", "Int", "Array", "List", "insert"
    , "isZero"
    , "map"
    -- CVC4:
    , "as", "concat"
    ]

