{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ViewPatterns #-}
module Tip.Pretty.SMT where

import Text.PrettyPrint

import Prelude hiding ((<>))
import Tip.Pretty
import Tip.Types
import Tip.Core (ifView, topsort, exprType, makeGlobal, uses, collectLets, theoryGoals)
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
    config_use_prove :: Bool,
    config_use_single_datatype :: Bool }
  deriving Show
data ProveMode = UseProve | UsePushPopAssert | UseAssert
  deriving (Eq, Show)

smtConfig, tipConfig :: Config
smtConfig =
  Config {
    config_keywords = smtKeywords,
    config_use_prove = False,
    config_use_single_datatype = False }
tipConfig =
  Config {
    config_keywords = [],
    config_use_prove = True,
    config_use_single_datatype = True }

ppTheory :: (Ord a,PrettyVar a) => Config -> Theory a -> Doc
ppTheory Config{..} thy =
  vcat $
    map ppSort thy_sorts ++
    map (ppDatas config_use_single_datatype) (topsort thy_datatypes) ++
    map ppUninterp thy_sigs ++
    map ppFuncs (topsort thy_funcs) ++
    map (ppFormula proveMode) thy_asserts
  where
    Theory{..} =
      renameAvoiding (tipKeywords ++ config_keywords) removeForbidden thy
    proveMode
      | config_use_prove = UseProve
      | length (theoryGoals thy) == 1 = UseAssert
      | otherwise = UsePushPopAssert
    removeForbidden xs@('.':_) = 'x':xs
    removeForbidden xs@('@':_) = 'x':xs
    removeForbidden xs = xs

ppSort :: PrettyVar a => Sort a -> Doc
ppSort (Sort sort attrs tvs) = parExpr "declare-sort" [sep [ppVarSMT sort, ppAttrs attrs], int (length tvs)]

ppDatas :: PrettyVar a => Bool -> [Datatype a] -> Doc
ppDatas single [datatype@(Datatype tycon attrs _ _)] | single =
  parExprSep "declare-datatype" [fsep [ppVarSMT tycon, ppAttrs attrs, ppData datatype]]

ppDatas _ datatypes@(Datatype tycon _ tyvars _:_) =
  parExprSep "declare-datatypes" [parens (fsep (map ppDTypeName datatypes)), parens (fsep (map ppData datatypes))]
ppDatas _ [] = error "empty scc"

ppDTypeName :: PrettyVar a => Datatype a -> Doc
ppDTypeName (Datatype tycon attrs tyvars _) =
  parExprSep (sep [ppVarSMT tycon, ppAttrs attrs]) [int (length tyvars)]

ppData :: PrettyVar a => Datatype a -> Doc
ppData (Datatype _ _ tyvars datacons) = par'' tyvars (fsep (map ppCon datacons))
--    parExprSep "par" [parens (fsep (map ppVarSMT tyvars)), parens (fsep (map ppCon datacons))]

ppCon :: PrettyVar a => Constructor a -> Doc
ppCon (Constructor datacon attrs selector args) =
  parExprSep (sep [ppVarSMT datacon, ppAttrs attrs]) [apply (ppVarSMT p) (ppType t) | (p,t) <- args]


par :: (PrettyVar a) => [a] -> Doc -> Doc
par [] d = d
par xs d = parExprSep "par" [parens (fsep (map ppVarSMT xs)), parens d]

par' :: (PrettyVar a) => [a] -> Doc -> Doc
par' [] d = d
par' xs d = parExprSep "par" [parens (fsep (map ppVarSMT xs)), d]

par'' :: (PrettyVar a) => [a] -> Doc -> Doc
par'' xs d = par' xs (parens d)

ppUninterp :: PrettyVar a => Signature a -> Doc
ppUninterp (Signature f attrs (PolyType tyvars arg_types result_type))
  | null arg_types =
    apply "declare-const"
      (sep [ppVarSMT f, ppAttrs attrs] $\ par' tyvars (ppType result_type))
  | otherwise =
    apply "declare-fun"
      (sep [ppVarSMT f, ppAttrs attrs] $\
        (par tyvars
          (sep [parens (fsep (map ppType arg_types)), ppType result_type])))

ppFuncs :: (Ord a, PrettyVar a) => [Function a] -> Doc
ppFuncs [f] =
      expr (if func_name f `elem` uses f
              then "define-fun-rec"
              else "define-fun")
           [ppFuncSig f (ppExpr (func_body f))]
ppFuncs fs = expr "define-funs-rec"
  [ parens (vcat [parens (ppFuncSig f empty) | f <- fs])
  , parens (vcat (map (ppExpr . func_body) fs))
  ]

ppFuncSig :: PrettyVar a => Function a -> Doc -> Doc
ppFuncSig (Function f attrs tyvars args res_ty body) content =
    sep [ppVarSMT f, ppAttrs attrs] $$ fsep [par tyvars (fsep  [ppLocals args, ppType res_ty]), content]

ppFormula :: (Ord a, PrettyVar a) => ProveMode -> Formula a -> Doc
ppFormula UseProve (Formula Prove attrs tvs term) =
  apply "prove" $
    ppAttrs attrs $$ par' tvs (ppExpr term)
ppFormula UseAssert (Formula Prove attrs tvs term) =
  apply "assert" (apply "not" (ppAttrs attrs $$ par' tvs (ppExpr term))) $$
  parens (text "check-sat")
ppFormula UsePushPopAssert form@(Formula Prove _ _ _) =
  vcat [
    apply "push" (text "1"),
    ppFormula UseAssert form,
    apply "pop" (text "1")]
ppFormula _ (Formula Assert attrs tvs term) =
  apply "assert" $
   ppAttrs attrs $$ par' tvs (ppExpr term)

ppExpr :: (Ord a, PrettyVar a) => Expr a -> Doc
ppExpr e | Just (c,t,f) <- ifView e = parExpr "ite" (map ppExpr [c,t,f])
ppExpr e@(hd@(Gbl Global{..}) :@: es)
  | isNothing (makeGlobal gbl_name gbl_type (map exprType es) Nothing) =
    exprSep (exprSep "_" (ppHead hd:map ppType gbl_args)) (map ppExpr es)
ppExpr (hd :@: es)  = exprSep (ppHead hd) (map ppExpr es)
ppExpr (Lcl l)      = ppVarSMT (lcl_name l)
ppExpr (Lam ls e)   = parExprSep "lambda" [ppLocals ls,ppExpr e]
ppExpr (Match e as) = "(match" $\ ppExpr e $\ (parens (vcat (map ppCase as)) <> ")")
ppExpr lets@Let{} =
  parExprSep "let"
    [ parens (vcat (map parens [ppVarSMT (lcl_name x) $\ ppExpr b | (x,b) <- bs]))
    , ppExpr e
    ]
  where (bs,e) = collectLets lets
ppExpr (LetRec fs e) =
  parExpr "letrec"
    [ parens (ppFuncs fs), ppExpr e ]
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

ppAttrs :: [Attribute] -> Doc
ppAttrs = fsep . map ppAttr

ppAttr :: Attribute -> Doc
ppAttr (name, Nothing) = ppKeyword name
ppAttr (name, Just x) = ppKeyword name <+> ppVarSMT x

ppKeyword :: String -> Doc
ppKeyword x = text (':':x)

-- Temporary use SMTLIB as the pretty printer:

instance (Ord a,PrettyVar a) => Pretty (Decl a) where
  pp (DataDecl d)   = ppDatas True [d]
  pp (SortDecl d)   = ppSort d
  pp (SigDecl d)    = ppUninterp d
  pp (FuncDecl d)   = ppFuncs [d]
  pp (AssertDecl d) = ppFormula UseProve d

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
  pp = ppFuncs . return

instance (Ord a, PrettyVar a) => Pretty (Formula a) where
  pp = ppFormula UseProve

instance PrettyVar a => Pretty (Datatype a) where
  pp = ppDatas True . return

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

-- Keywords which can be used but must be quoted
smtQuoted :: [String]
smtQuoted = [
  "check-sat", "assert", "assert-not", "declare-datatypes",
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
