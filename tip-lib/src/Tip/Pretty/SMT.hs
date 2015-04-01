{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards #-}
module Tip.Pretty.SMT where

import Text.PrettyPrint

import Tip.Pretty
import Tip.Types
import Tip (ifView, topsort)

expr,parExpr :: Doc -> [Doc] -> Doc
parExpr s [] = "(" <> s <> ")"
parExpr s xs = ("(" <> s) $\ fsep (init xs ++ [last xs<>")"])

expr s [] = s
expr s xs = parExpr s xs

apply :: Doc -> Doc -> Doc
apply s x = parExpr s [x]

ppTheory :: (Ord a,Pretty a) => Theory a -> Doc
ppTheory Theory{..}
  = vcat
     (map ppSort thy_abs_type_decls ++
      map ppDatas (topsort thy_data_decls) ++
      map ppUninterp thy_abs_func_decls ++
      map ppFuncs (topsort thy_func_decls) ++
      map ppFormula thy_form_decls ++
      ["(check-sat)"])

ppSort :: Pretty a => AbsType a -> Doc
ppSort (AbsType sort) = parExpr "declare-sort" [pp sort, text "0"]

ppDatas :: Pretty a => [Datatype a] -> Doc
ppDatas datatypes@(Datatype _ tyvars _:_) =
  parExpr "declare-datatypes" [parens (fsep (map pp tyvars)), parens (fsep (map ppData datatypes))]

ppData :: Pretty a => Datatype a -> Doc
ppData (Datatype tycon _ datacons) =
  parExpr (pp tycon) (map ppCon datacons)

ppCon :: Pretty a => Constructor a -> Doc
ppCon (Constructor datacon _ args) =
  parExpr (pp datacon) [apply (pp p) (ppType t) | (p,t) <- args]

par :: Pretty a => [a] -> Doc -> Doc
par [] d = d
par xs d = parExpr "par" [parens (fsep (map pp xs)), parens d]

ppUninterp :: Pretty a => AbsFunc a -> Doc
ppUninterp (AbsFunc f (PolyType tyvars arg_types result_type)) =
  apply "declare-fun"
    (par tyvars
      (apply (pp f)
        (sep [parens (fsep (map ppType arg_types)), ppType result_type])))

ppFuncs :: Pretty a => [Function a] -> Doc
ppFuncs fs = apply "define-fun-rec" (parens (vcat (map ppFunc fs)))

ppFunc :: Pretty a => Function a -> Doc
ppFunc (Function f tyvars args res_ty body) =
  parens (par tyvars
    (pp f $\ fsep [ppLocals args, ppType res_ty, ppExpr body]))

ppFormula :: Pretty a => Formula a -> Doc
ppFormula (Formula role tyvars term) =
  ppRole role (par tyvars (ppExpr term))

ppRole :: Role -> Doc -> Doc
ppRole Assert d = apply "assert" d
ppRole Prove  d = apply "assert" (apply "not" d)

ppExpr :: Pretty a => Expr a -> Doc
ppExpr e | Just (c,t,f) <- ifView e = parExpr "ite" (map ppExpr [c,t,f])
ppExpr (hd :@: es)  = expr (ppHead hd) (map ppExpr es)
ppExpr (Lcl l)      = pp (lcl_name l)
ppExpr (Lam ls e)   = parExpr "lambda" [ppLocals ls,ppExpr e]
ppExpr (Match e as) = "(match" $\ ppExpr e $\ (vcat (map ppCase as) <> ")")
ppExpr (Let x b e)  = parExpr "let" [parens (ppLocal x $\ ppExpr b), ppExpr e]
ppExpr (Quant _ q ls e) = parExpr (ppQuant q) [ppLocals ls, ppExpr e]

ppLocals :: Pretty a => [Local a] -> Doc
ppLocals ls = parens (fsep (map ppLocal ls))

ppLocal :: Pretty a => Local a -> Doc
ppLocal (Local l t) = expr (pp l) [ppType t]

ppHead :: Pretty a => Head a -> Doc
ppHead (Gbl gbl)   = pp (gbl_name gbl)
ppHead (Builtin b) = ppBuiltin b

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

ppCase :: Pretty a => Case a -> Doc
ppCase (Case pat rhs) = parExpr "case" [ppPat pat,ppExpr rhs]

ppPat :: Pretty a => Pattern a -> Doc
ppPat Default         = "default"
ppPat (ConPat g [])   = pp (gbl_name g)
ppPat (ConPat g args) = parExpr (pp (gbl_name g)) [pp (lcl_name arg) | arg <- args]
ppPat (LitPat lit)    = ppLit lit

ppType :: Pretty a => Type a -> Doc
ppType (TyVar x)     = pp x
ppType (TyCon tc ts) = expr (pp tc) (map ppType ts)
ppType (ts :=>: r)   = parExpr "=>" (map ppType (ts ++ [r]))
ppType NoType        = "_"
ppType (BuiltinType Integer) = "int"
ppType (BuiltinType Boolean) = "bool"

-- Temporary use SMTLIB as the pretty printer:

instance (Ord a,Pretty a) => Pretty (Theory a) where
  pp = ppTheory

instance Pretty a => Pretty (Expr a) where
  pp = ppExpr

instance Pretty a => Pretty (Type a) where
  pp = ppType

instance Pretty a => Pretty (Function a) where
  pp = ppFunc

instance Pretty a => Pretty (Formula a) where
  pp = ppFormula

