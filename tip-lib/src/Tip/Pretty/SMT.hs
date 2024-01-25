{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ViewPatterns #-}
module Tip.Pretty.SMT where

import Text.PrettyPrint

import Prelude hiding ((<>))
import Tip.Pretty
import Tip.Types
import Tip.Core (ifView, topsort, exprType, makeGlobal, uses, collectLets, theoryGoals, hasAttr, lemma)
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

ppVarSMT :: PrettyVar a => a -> Doc
ppVarSMT x
  | isValidSMTString str && str `notElem` (smtQuoted ++ tipKeywords) =
    -- N.B.: although variables names cannot come from tipKeywords,
    -- attribute values can, and they are also printed using ppVarSMT
    text str
  | otherwise = text ("|" ++ concatMap escape str ++ "|")
  where
    str = varStr x
    escape '\\' = "backslash"
    escape '|' = "bar"
    escape x = [x]

isValidSMTString :: String -> Bool
isValidSMTString [] = False
isValidSMTString (x:xs)
  | x `elem` ("-0123456789" :: String) = False
isValidSMTString xs =
  and [ isAlphaNum x || x `elem` ("~!@$%^&*_-+=<>.?/" :: String) | x <- xs ]

data Config =
  Config {
    config_keywords :: [String],
    config_prove_mode :: ProveMode,
    config_use_single_datatype :: Bool,
    config_print_attrs :: Bool }
  deriving Show
data ProveMode = UseProve | UsePushPopAssert | UseAssert | UseAssertClaims 
  deriving (Eq, Show)

smtConfig, tipConfig, vampConfig :: Config
smtConfig =
  Config {
    config_keywords = smtKeywords,
    config_prove_mode = UsePushPopAssert,
    config_use_single_datatype = False,
    config_print_attrs = False }
tipConfig =
  Config {
    config_keywords = [],
    config_prove_mode = UseProve,
    config_use_single_datatype = True,
    config_print_attrs = True }
vampConfig =
  Config {
    config_keywords = smtKeywords,
    config_prove_mode = UseAssertClaims,
    config_use_single_datatype = True,
    config_print_attrs = False }
    
ppTheory :: (Ord a,PrettyVar a) => Config -> Theory a -> Doc
ppTheory cfg0 thy =
  vcat $
    map (ppSort cfg) thy_sorts ++
    map (ppDatas cfg) (topsort thy_datatypes) ++
    map (ppUninterp cfg) thy_sigs ++
    map (ppFuncs cfg) (topsort thy_funcs) ++
    map (ppFormula cfg) thy_asserts
  where
    cfg = cfg0 { config_prove_mode = eliminatePushPop (config_prove_mode cfg0) }
    eliminatePushPop UsePushPopAssert | length (theoryGoals thy) == 1 = UseAssert
    eliminatePushPop mode = mode

    Theory{..} =
      renameAvoiding (tipKeywords ++ config_keywords cfg) removeForbidden thy
    removeForbidden xs@('.':_) = 'x':xs
    removeForbidden xs@('@':_) = 'x':xs
    removeForbidden xs = xs

ppSort :: PrettyVar a => Config -> Sort a -> Doc
ppSort cfg (Sort sort attrs tvs) = parExpr "declare-sort" [sep [ppVarSMT sort, ppAttrs cfg attrs], int (length tvs)]

ppDatas :: PrettyVar a => Config -> [Datatype a] -> Doc
ppDatas cfg@Config{..} [datatype@(Datatype tycon attrs _ _)] | config_use_single_datatype =
  parExprSep "declare-datatype" [fsep [ppVarSMT tycon, ppAttrs cfg attrs, ppData cfg datatype]]

ppDatas cfg datatypes@(Datatype tycon _ tyvars _:_) =
  parExprSep "declare-datatypes" [parens (fsep (map (ppDTypeName cfg) datatypes)), parens (fsep (map (ppData cfg) datatypes))]
ppDatas _ [] = error "empty scc"

ppDTypeName :: PrettyVar a => Config -> Datatype a -> Doc
ppDTypeName cfg (Datatype tycon attrs tyvars _) =
  parExprSep (sep [ppVarSMT tycon, ppAttrs cfg attrs]) [int (length tyvars)]

ppData :: PrettyVar a => Config -> Datatype a -> Doc
ppData cfg (Datatype _ _ tyvars datacons) = par'' tyvars (fsep (map (ppCon cfg) datacons))
--    parExprSep "par" [parens (fsep (map ppVarSMT tyvars)), parens (fsep (map ppCon datacons))]

ppCon :: PrettyVar a => Config -> Constructor a -> Doc
ppCon cfg (Constructor datacon attrs selector args) =
  parExprSep (sep [ppVarSMT datacon, ppAttrs cfg attrs]) [apply (ppVarSMT p) (ppType t) | (p,t) <- args]


par :: (PrettyVar a) => [a] -> Doc -> Doc
par [] d = d
par xs d = parExprSep "par" [parens (fsep (map ppVarSMT xs)), parens d]

par' :: (PrettyVar a) => [a] -> Doc -> Doc
par' [] d = d
par' xs d = parExprSep "par" [parens (fsep (map ppVarSMT xs)), d]

par'' :: (PrettyVar a) => [a] -> Doc -> Doc
par'' xs d = par' xs (parens d)

ppUninterp :: PrettyVar a => Config -> Signature a -> Doc
ppUninterp cfg (Signature f attrs (PolyType tyvars arg_types result_type))
  | null arg_types =
    apply "declare-const"
      (sep [ppVarSMT f, ppAttrs cfg attrs] $\ par' tyvars (ppType result_type))
  | otherwise =
    apply "declare-fun"
      (sep [ppVarSMT f, ppAttrs cfg attrs] $\
        (par tyvars
          (sep [parens (fsep (map ppType arg_types)), ppType result_type])))

ppFuncs :: (Ord a, PrettyVar a) => Config -> [Function a] -> Doc
ppFuncs cfg [f] =
      expr (if func_name f `elem` uses f
              then "define-fun-rec"
              else "define-fun")
           [ppFuncSig cfg f (ppExpr (func_body f))]
ppFuncs cfg fs = expr "define-funs-rec"
  [ parens (vcat [parens (ppFuncSig cfg f empty) | f <- fs])
  , parens (vcat (map (ppExpr . func_body) fs))
  ]

ppFuncSig :: PrettyVar a => Config -> Function a -> Doc -> Doc
ppFuncSig cfg (Function f attrs tyvars args res_ty body) content =
    sep [ppVarSMT f, ppAttrs cfg attrs] $$ fsep [par tyvars (fsep [ppLocals args, ppType res_ty]), content]

ppFormula :: (Ord a, PrettyVar a) => Config -> Formula a -> Doc
ppFormula cfg form@(Formula Prove attrs tvs term) =
  case config_prove_mode cfg of
    UseProve ->
      apply "prove" $
        ppAttrs cfg attrs $$ par' tvs (ppExpr term)
    UseAssert ->
      apply "assert" (apply "not" (ppAttrs cfg attrs $$ par' tvs (ppExpr term))) $$
      parens (text "check-sat")
    UsePushPopAssert ->
      vcat [
        apply "push" (text "1"),
        ppFormula cfg{config_prove_mode = UseAssert} form,
        apply "pop" (text "1")]
    UseAssertClaims ->
      if (hasAttr lemma attrs) then
        apply "assert-claim" (ppAttrs cfg attrs $$ par' tvs (ppExpr term))
      else apply "assert-not" (ppAttrs cfg attrs $$ par' tvs (ppExpr term))
ppFormula cfg (Formula Assert attrs tvs term) =
  apply "assert" $
   ppAttrs cfg attrs $$ par' tvs (ppExpr term)

ppExpr :: (Ord a, PrettyVar a) => Expr a -> Doc
ppExpr e | Just (c,t,f) <- ifView e = parExpr "ite" (map ppExpr [c,t,f])
ppExpr e@(hd@(Gbl Global{..}) :@: es)
  | isNothing (makeGlobal gbl_name gbl_type (map exprType es) Nothing) =
    exprSep (exprSep "_" (ppHead hd:map ppType gbl_args)) (map ppExpr es)
ppExpr (hd :@: es)  = exprSep (ppHead hd) (map ppExpr es)
ppExpr (Lcl l)      = ppVarSMT (lcl_name l)
ppExpr (Lam ls e)   = parExprSep "lambda" [ppLocals ls,ppExpr e]
ppExpr (Match e as) = "(match" $\ ppExpr e $\ (parens (vcat (map ppCase (sortCases as))) <> ")")
  where
    -- Default pattern must come last in SMTLIB
    sortCases (a@Case{case_pat = Default}:as) = as ++ [a]
    sortCases as = as
ppExpr lets@Let{} =
  parExprSep "let"
    [ parens (vcat (map parens [ppVarSMT (lcl_name x) $\ ppExpr b | (x,b) <- bs]))
    , ppExpr e
    ]
  where (bs,e) = collectLets lets
ppExpr (LetRec fs e) =
  parExpr "letrec"
    -- HACK: use tipConfig when printing letrec.
    -- letrec is not allowed in tip files anyway, only in intermediate code.
    [ parens (ppFuncs tipConfig fs), ppExpr e ]
ppExpr (Quant _ q ls e) = parExprSep (ppQuant q) [ppLocals ls, ppExpr e]

ppLocals :: PrettyVar a => [Local a] -> Doc
ppLocals ls = parens (fsep (map ppLocal ls))

ppLocal :: PrettyVar a => Local a -> Doc
ppLocal (Local l t) = expr (ppVarSMT l) [ppType t]

ppHead :: PrettyVar a => Head a -> Doc
ppHead (Builtin b) = ppBuiltin b
ppHead (Gbl gbl)   = ppVarSMT (gbl_name gbl) {- -- $$ ";" <> ppPolyType (gbl_type gbl)
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
ppBuiltin NumAdd    = "+"
ppBuiltin NumSub    = "-"
ppBuiltin NumMul    = "*"
ppBuiltin NumDiv    = "/"
ppBuiltin IntDiv    = "div"
ppBuiltin IntMod    = "mod"
ppBuiltin NumGt     = ">"
ppBuiltin NumGe     = ">="
ppBuiltin NumLt     = "<"
ppBuiltin NumLe     = "<="
ppBuiltin At{}      = "@"
ppBuiltin NumWiden  = "to_real"

ppLit :: Lit -> Doc
ppLit (Int i)      = integer i
ppLit (Bool True)  = "true"
ppLit (Bool False) = "false"

ppQuant :: Quant -> Doc
ppQuant Forall = "forall"
ppQuant Exists = "exists"

ppCase :: (Ord a, PrettyVar a) => Case a -> Doc
ppCase (Case pat rhs) = parens (fsep [ppPat pat, ppExpr rhs])

ppPat :: PrettyVar a => Pattern a -> Doc
ppPat Default         = "_"
ppPat (ConPat g args) = expr (ppVarSMT (gbl_name g)) [ppVarSMT (lcl_name arg) | arg <- args]
ppPat (LitPat lit)    = ppLit lit

ppType :: PrettyVar a => Type a -> Doc
ppType (TyVar x)     = ppVarSMT x
ppType (TyCon tc ts) = expr (ppVarSMT tc) (map ppType ts)
ppType (ts :=>: r)   = parExpr "=>" (map ppType (ts ++ [r]))
ppType (BuiltinType bu) = ppBuiltinType bu

ppBuiltinType :: BuiltinType -> Doc
ppBuiltinType Integer = "Int"
ppBuiltinType Real    = "Real"
ppBuiltinType Boolean = "Bool"

ppAttrs :: Config -> [Attribute] -> Doc
ppAttrs cfg attrs
  | config_print_attrs cfg = fsep (map ppAttr attrs)
  | otherwise = empty

ppAttr :: Attribute -> Doc
ppAttr (name, Nothing) = ppKeyword name
ppAttr (name, Just x) = ppKeyword name <+> ppVarSMT x

ppKeyword :: String -> Doc
ppKeyword x = text (':':x)

-- Temporary use SMTLIB as the pretty printer:

instance (Ord a,PrettyVar a) => Pretty (Decl a) where
  pp (DataDecl d)   = ppDatas tipConfig [d]
  pp (SortDecl d)   = ppSort tipConfig d
  pp (SigDecl d)    = ppUninterp tipConfig d
  pp (FuncDecl d)   = ppFuncs tipConfig [d]
  pp (AssertDecl d) = ppFormula tipConfig d

instance (Ord a,PrettyVar a) => Pretty (Theory a) where
  pp = ppTheory tipConfig

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
  pp = ppFuncs tipConfig . return

instance (Ord a, PrettyVar a) => Pretty (Formula a) where
  pp = ppFormula tipConfig

instance PrettyVar a => Pretty (Datatype a) where
  pp = ppDatas tipConfig . return

instance PrettyVar a => Pretty (Sort a) where
  pp = ppSort tipConfig

instance PrettyVar a => Pretty (Signature a) where
  pp = ppUninterp tipConfig

instance PrettyVar a => Pretty (Local a) where
  pp = ppLocal

instance PrettyVar a => Pretty (Global a) where
  pp = ppHead . Gbl

instance PrettyVar a => Pretty (Head a) where
  pp = ppHead

instance PrettyVar a => Pretty (Pattern a) where
  pp = ppPat

-- Keywords which can be used but must be quoted
smtQuoted :: [String]
smtQuoted = [
  "check-sat", "assert", "assert-not", "assert-claim", "declare-datatypes",
  "declare-sort", "declare-const", "declare-fun", "define-fun",
  "define-fun-rec", "define-funs-rec", "par", "case"]

-- Keywords which can not be used at all in TIP
-- (e.g. predefined types and functions)
tipKeywords :: [String]
tipKeywords = [
  "Int", "Real", "Bool", "as", "match", "let", "true", "false",
  "lambda", "forall", "exists", "@", "ite", "if", "and", "or", "not",
  "=>", "=", "equals", "distinct", "+", "-", "*", "/", "div", "mod",
  ">", ">=", "<", "<=", "to_real", "!"]

-- Keywords which can not be used at all in some SMT solvers
smtKeywords :: [String]
smtKeywords = [
  "abs", "Array", "List", "insert", "isZero", "map", "select",
  "subset", "union", "intersect", "concat", "member",
  "exp", "store"]
