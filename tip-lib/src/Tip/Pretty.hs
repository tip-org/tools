{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
module Tip.Pretty where

import Text.PrettyPrint

import Tip

infixr 1 $\

($\) :: Doc -> Doc -> Doc
d1 $\ d2 = hang d1 2 d2

expr,parExpr :: Doc -> [Doc] -> Doc
parExpr s [] = "(" <> s <> ")"
parExpr s xs = ("(" <> s) $\ fsep (init xs ++ [last xs<>")"])

expr s [] = s
expr s xs = parExpr s xs

class Show a => Pretty a where
  pp :: a -> Doc

ppRender :: Pretty a => a -> String
ppRender = render . pp

instance Pretty a => Pretty (Local a) where
  pp (Local l t) = expr (pp l) [pp t]

instance Pretty a => Pretty (Head a) where
  pp (Gbl gbl)   = pp (gbl_name gbl)
  pp (Builtin b) = pp b

instance Pretty a => Pretty (Expr a) where
  pp (hd :@: es)    = expr (pp hd) (map pp es)
  pp (Lcl l)        = pp (lcl_name l)
  pp (Lam ls e)     = parExpr "lambda" [parens (fsep (map pp ls)),pp e]
  pp (Match e as)   = parens (("match" $\ pp e) $\ vcat (map pp as))
  pp (Let x b e)    = parExpr "let" [parens (pp x),parens (pp b),parens (pp e)]
  pp (Quant q l e) = parExpr (pp q) [parens (pp l),parens (pp e)]

instance Pretty Quant where
  pp Forall = "forall"
  pp Exists = "exists"

instance Pretty Builtin where
  pp (Lit lit) = pp lit
  pp And      = "and"
  pp Or       = "or"
  pp Implies  = "=>"
  pp Equal    = "="
  pp Distinct = "distinct"
  pp At{}     = "@"

instance Pretty a => Pretty (Case a) where
  pp (Case p e) = parExpr "case" [pp p,pp e]

instance Pretty a => Pretty (Pattern a) where
  pp Default       = "default"
  pp (ConPat g []) = pp (gbl_name g)
  pp (ConPat g as) = parExpr (pp (gbl_name g)) (map (pp . lcl_name) as)
  pp (LitPat lit)  = pp lit

instance Pretty Lit where
  pp (Int i)    = integer i
  pp (Bool b)   = pp b
  pp (String s) = text (show s)

instance Pretty Bool where
  pp True  = "true"
  pp False = "false"

instance Pretty a => Pretty (Type a) where
  pp (TyVar x)        = pp x
  pp (TyCon tc ts)    = expr (pp tc) (map pp ts)
  pp (ts :=>: r)      = parExpr "=>" (map pp (ts ++ [r]))
  pp (BuiltinType bt) = pp bt

instance Pretty BuiltinType where
  pp Integer = "int"
  pp Boolean = "bool"

instance Pretty a => Pretty (Function a) where
  pp Function{..} = parens $
    (("define-fun" $\ parNonempty func_tvs $\ pp func_name)
      $\ sep [parens (fsep (map pp func_args)),pp func_res])
      $\ pp func_body

parNonempty :: Pretty a => [a] -> Doc
parNonempty [] = empty
parNonempty xs = parens (fsep (map pp xs))

instance Pretty a => Pretty (Datatype a) where
  pp Datatype{..} = parens $
    ("declare-datatype" $\ parNonempty data_tvs $\ pp data_name)
      $\ fsep (map pp data_cons)

instance Pretty a => Pretty (Constructor a) where
  pp Constructor{..} = expr (pp con_name) (map pp con_args)

instance Pretty a => Pretty (Formula a) where
  pp (Formula role tvs tm) = parens $ (pp role $\ parNonempty tvs) $\ pp tm

instance Pretty Role where
  pp Assert = "assert"
  pp Prove  = "prove"

instance Pretty a => Pretty (Theory a) where
  pp (Theory ds fns fms) = vcat (map pp ds ++ map pp fns ++ map pp fms)

