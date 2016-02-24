{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ViewPatterns #-}
module Tip.Pretty.SMT where

import Text.PrettyPrint

import Tip.Pretty
import Tip.Types
import Tip.Core (ifView, topsort, neg, exprType, makeGlobal, uses, collectLets)
import Tip.Rename
import Data.Maybe
import Data.Char (isAlphaNum)

expr,parExpr,parExprSep :: Doc -> [Doc] -> Doc
parExpr s [] = parens s
parExpr s xs = ("(" <> s) $\ (fsep xs <> ")")

parExprSep s [x]    = ("(" <> s) $\ (x <> ")")
parExprSep s (x:xs) = (("(" <> s) $\ x) $\ (fsep xs <> ")")
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
     (map ppSort thy_sorts ++
      map ppDatas (topsort thy_datatypes) ++
      map ppUninterp thy_sigs ++
      map ppFuncs (topsort thy_funcs) ++
      map ppFormula thy_asserts ++
      ["(check-sat)"])

ppSort :: PrettyVar a => Sort a -> Doc
ppSort (Sort sort tvs) = parExpr "declare-sort" [ppVar sort, int (length tvs)]

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

par'' :: (PrettyVar a) => [a] -> Doc -> Doc
par'' xs d = par' xs (parens d)

ppUninterp :: PrettyVar a => Signature a -> Doc
ppUninterp (Signature f (PolyType tyvars arg_types result_type)) =
  apply (if null arg_types then "declare-const" else "declare-fun")
    (par tyvars
      (ppVar f $\
        (sep [ if null arg_types then empty else parens (fsep (map ppType arg_types))
             , ppType result_type
             ])))

ppFuncs :: (Ord a, PrettyVar a) => [Function a] -> Doc
ppFuncs [f] =
      expr (if func_name f `elem` uses f
              then "define-fun-rec"
              else "define-fun")
           [ppFuncSig par f (ppExpr (func_body f))]
ppFuncs fs = expr "define-funs-rec"
  [ parens (vcat [ppFuncSig par'' f empty | f <- fs])
  , parens (vcat (map (ppExpr . func_body) fs))
  ]

ppFuncSig :: PrettyVar a => ([a] -> Doc -> Doc) -> Function a -> Doc -> Doc
ppFuncSig parv (Function f tyvars args res_ty body) content =
  parv tyvars (ppVar f $\ fsep [ppLocals args, ppType res_ty, content])

ppFormula :: (Ord a, PrettyVar a) => Formula a -> Doc
ppFormula (Formula Prove _ _ tvs term)  = apply "assert-not" (par' tvs (ppExpr term))
ppFormula (Formula Assert _ _ tvs term) = apply "assert"     (par' tvs (ppExpr term))

ppExpr :: (Ord a, PrettyVar a) => Expr a -> Doc
ppExpr e | Just (c,t,f) <- ifView e = parExpr "ite" (map ppExpr [c,t,f])
ppExpr e@(hd@(Gbl Global{..}) :@: es)
  | isNothing (makeGlobal gbl_name gbl_type (map exprType es) Nothing)
      = exprSep "as" [exprSep (ppHead hd) (map ppExpr es), ppType (exprType e)]
ppExpr (hd :@: es)  = exprSep (ppHead hd) (map ppExpr es)
ppExpr (Lcl l)      = ppVar (lcl_name l)
ppExpr (Lam ls e)   = parExprSep "lambda" [ppLocals ls,ppExpr e]
ppExpr (Match e as) = "(match" $\ ppExpr e $\ (vcat (map ppCase as) <> ")")
ppExpr lets@Let{} =
  parExprSep "let"
    [ parens (vcat (map parens [ppVar (lcl_name x) $\ ppExpr b | (x,b) <- bs]))
    , ppExpr e
    ]
  where (bs,e) = collectLets lets
ppExpr (Quant _ q ls e) = parExprSep (ppQuant q) [ppLocals ls, ppExpr e]

ppLocals :: PrettyVar a => [Local a] -> Doc
ppLocals ls = parens (fsep (map ppLocal ls))

ppLocal :: PrettyVar a => Local a -> Doc
ppLocal (Local l t) = expr (ppVar l) [ppType t]

ppHead :: PrettyVar a => Head a -> Doc
ppHead (Builtin b) = ppBuiltin b
ppHead (Gbl gbl)   = ppVar (gbl_name gbl) {- -- $$ ";" <> ppPolyType (gbl_type gbl)
                                             -- $$ ";" <> fsep (map ppType (gbl_args gbl))
                                             -- $$ text ""
                                          -}

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
ppBuiltin IntDiv    = "div"
ppBuiltin IntMod    = "mod"
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
ppType (BuiltinType bu) = ppBuiltinType bu

ppBuiltinType :: BuiltinType -> Doc
ppBuiltinType Integer = "Int"
ppBuiltinType Boolean = "Bool"

-- Temporary use SMTLIB as the pretty printer:

instance (Ord a,PrettyVar a) => Pretty (Decl a) where
  pp (DataDecl d)   = ppData d
  pp (SortDecl d)   = ppSort d
  pp (SigDecl d)    = ppUninterp d
  pp (FuncDecl d)   = ppFuncs [d]
  pp (AssertDecl d) = ppFormula d

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

instance PrettyVar a => Pretty (Sort a) where
  pp = ppSort

instance PrettyVar a => Pretty (Signature a) where
  pp = ppUninterp

instance PrettyVar a => Pretty (Local a) where
  pp = ppLocal

instance PrettyVar a => Pretty (Global a) where
  pp = ppHead . Gbl

instance PrettyVar a => Pretty (Head a) where
  pp = ppHead

instance PrettyVar a => Pretty (Pattern a) where
  pp = ppPat

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
    , "mod", "div"
    , "=", "=>", "+", "-", "*", ">", ">=", "<", "<=", "@", "!"
    , "as"
    , "declare-datatypes"
    , "declare-sort"
    , "declare-const"
    , "declare-const"
    , "declare-fun"
    , "declare-fun"
    , "define-fun"
    , "define-fun"
    , "define-fun-rec"
    , "define-fun-rec"
    , "define-funs-rec"
    , "check-sat"
    -- TIP:
    , "par"
    , "case"
    , "match"
    , "assert"
    , "assert-not"
    -- Z3:
    , "Bool", "Int", "Array", "List", "insert"
    , "isZero"
    , "map"
    , "select"
    , "subset", "union", "intersect"
    -- CVC4:
    , "concat", "member"
    ]
