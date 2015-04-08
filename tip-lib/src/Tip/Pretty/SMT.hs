{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards #-}
module Tip.Pretty.SMT where

import Text.PrettyPrint

import Tip.Pretty
import Tip.Types
import Tip (ifView, topsort, neg)

expr,parExpr :: Doc -> [Doc] -> Doc
parExpr s [] = "(" <> s <> ")"
parExpr s xs = ("(" <> s) $\ fsep (init xs ++ [last xs<>")"])

expr s [] = s
expr s xs = parExpr s xs

apply :: Doc -> Doc -> Doc
apply s x = parExpr s [x]

ppTheory :: (Ord a,PrettyVar a) => Theory a -> Doc
ppTheory Theory{..}
  = vcat
     (map ppSort thy_abs_type_decls ++
      map ppDatas (topsort thy_data_decls) ++
      map ppUninterp thy_abs_func_decls ++
      map ppFuncs (topsort thy_func_decls) ++
      map ppFormula thy_form_decls ++
      ["(check-sat)"])

ppSort :: PrettyVar a => AbsType a -> Doc
ppSort (AbsType sort) = parExpr "declare-sort" [ppVar sort, text "0"]

ppDatas :: PrettyVar a => [Datatype a] -> Doc
ppDatas datatypes@(Datatype _ tyvars _:_) =
  parExpr "declare-datatypes" [parens (fsep (map ppVar tyvars)), parens (fsep (map ppData datatypes))]

ppData :: PrettyVar a => Datatype a -> Doc
ppData (Datatype tycon _ datacons) =
  parExpr (ppVar tycon) (map ppCon datacons)

ppCon :: PrettyVar a => Constructor a -> Doc
ppCon (Constructor datacon _ args) =
  parExpr (ppVar datacon) [apply (ppVar p) (ppType t) | (p,t) <- args]

par :: PrettyVar a => [a] -> Doc -> Doc
par [] d = d
par xs d = parExpr "par" [parens (fsep (map ppVar xs)), parens d]

ppUninterp :: PrettyVar a => AbsFunc a -> Doc
ppUninterp (AbsFunc f (PolyType tyvars arg_types result_type)) =
  apply "declare-fun"
    (par tyvars
      (apply (ppVar f)
        (sep [parens (fsep (map ppType arg_types)), ppType result_type])))

ppFuncs :: PrettyVar a => [Function a] -> Doc
ppFuncs fs = apply "define-funs-rec" (parens (vcat (map ppFunc fs)))

ppFunc :: PrettyVar a => Function a -> Doc
ppFunc (Function f tyvars args res_ty body) =
  (par tyvars
    (ppVar f $\ fsep [ppLocals args, ppType res_ty, ppExpr body]))

ppFormula :: PrettyVar a => Formula a -> Doc
ppFormula (Formula Prove tvs term) =  vcat (map (ppSort . AbsType) tvs)
                                   $$ ppFormula (Formula Assert [] (neg term))
ppFormula (Formula Assert tvs term) = apply "assert" (par tvs (ppExpr term))

ppExpr :: PrettyVar a => Expr a -> Doc
ppExpr e | Just (c,t,f) <- ifView e = parExpr "ite" (map ppExpr [c,t,f])
ppExpr (hd :@: es)  = expr (ppHead hd) (map ppExpr es)
ppExpr (Lcl l)      = ppVar (lcl_name l)
ppExpr (Lam ls e)   = parExpr "lambda" [ppLocals ls,ppExpr e]
ppExpr (Match e as) = "(match" $\ ppExpr e $\ (vcat (map ppCase as) <> ")")
ppExpr (Let x b e)  = parExpr "let" [parens (ppLocal x $\ ppExpr b), ppExpr e]
ppExpr (Quant _ q ls e) = parExpr (ppQuant q) [ppLocals ls, ppExpr e]

ppLocals :: PrettyVar a => [Local a] -> Doc
ppLocals ls = parens (fsep (map ppLocal ls))

ppLocal :: PrettyVar a => Local a -> Doc
ppLocal (Local l t) = expr (ppVar l) [ppType t]

ppHead :: PrettyVar a => Head a -> Doc
ppHead (Gbl gbl)   = ppVar (gbl_name gbl)
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

ppCase :: PrettyVar a => Case a -> Doc
ppCase (Case pat rhs) = parExpr "case" [ppPat pat,ppExpr rhs]

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

instance PrettyVar a => Pretty (Expr a) where
  pp = ppExpr

instance PrettyVar a => Pretty (Type a) where
  pp = ppType

instance PrettyVar a => Pretty (Function a) where
  pp = ppFunc

instance PrettyVar a => Pretty (Formula a) where
  pp = ppFormula

