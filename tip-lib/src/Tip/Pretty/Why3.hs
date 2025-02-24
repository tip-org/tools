{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ScopedTypeVariables, ViewPatterns #-}
module Tip.Pretty.Why3 where

import Text.PrettyPrint

import Prelude hiding ((<>))
import Tip.Pretty
import Tip.Types
import Tip.Rename
import Tip.Core (ifView, DeepPattern(..), patternMatchingView, topsort, makeGlobal, exprType)

import Data.Char
import Data.Maybe

import Data.Generics.Geniplate

import qualified Data.Set as S

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
  cons = S.fromList (map con_name (universeBi thy))
  mk x = Why3Var (x `S.member` cons) x

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

ppTheory :: (Ord a,PrettyVar a) => Theory a -> Doc
ppTheory (renameAvoiding why3Keywords (filter isAlphaNum) . why3VarTheory -> Theory{..})
  = block ("module" <+> "A") $
    vcat (
      "use HighOrd" :
      "use import int.Int" :
      "use import int.EuclideanDivision" :
      "use import real.RealInfix" :
      "use import real.FromInt" :
      map ppSort thy_sorts ++
      map ppDatas (topsort thy_datatypes) ++
      map ppUninterp thy_sigs ++
      map ppFuncs (topsort thy_funcs) ++
      zipWith ppFormula thy_asserts [0..])

ppSort :: (PrettyVar a, Ord a) => Sort a -> Doc
ppSort (Sort sort _ []) = "type" $\ ppVar sort
ppSort (Sort sort _ n) =
  error $ "Can't translate abstract sort " ++ show (ppVar sort) ++ " of arity " ++ show (length n) ++ " to Why3"

ppDatas :: (PrettyVar a, Ord a) => [Datatype a] -> Doc
ppDatas (d:ds) = vcat (ppData "type" d:map (ppData "with") ds)
ppDatas [] = error "empty scc"

ppData :: (PrettyVar a, Ord a) => Doc -> Datatype a -> Doc
ppData header (Datatype tc _ tvs cons) =
  header $\ (ppVar tc $\ sep (map ppTyVar tvs) $\
    separating fsep ("=":repeat "|") (map ppCon cons))

ppCon :: (PrettyVar a, Ord a) => Constructor a -> Doc
ppCon (Constructor c _ _d as) = ppVar c <+> fsep (map (ppType 1 . snd) as)

ppQuant :: (PrettyVar a, Ord a) => Bool -> Doc -> [Local a] -> Doc -> Doc
ppQuant b _name [] d = d
ppQuant b name ls d = if b 
  then (name $\ fsep (punctuate "," (map (parens . ppLocalBinder) ls)) <+> "->") $\ d 
  else (name $\ fsep (punctuate "," (map ppLocalBinder ls)) <+> ".") $\ d 

ppBinder :: (PrettyVar a, Ord a) => a -> Type a -> Doc
ppBinder x t = ppVar x <+> ":" $\ ppType 0 t 

ppLocalBinder :: (PrettyVar a, Ord a) => Local a -> Doc
ppLocalBinder (Local x t) = ppBinder x t

ppUninterp :: (PrettyVar a, Ord a) => Signature a -> Doc
ppUninterp (Signature f  _(PolyType _ arg_types result_type)) =
  "function" $\ ppVar f $\ fsep (map (ppType 1) arg_types) $\ (":" <+> ppType 1 result_type)

ppFuncs :: (PrettyVar a, Ord a) => [Function a] -> Doc
ppFuncs (fn:fns) = vcat (ppFunc "function" fn:map (ppFunc "with") fns)
ppFuncs [] = error "empty scc"

ppFunc :: (PrettyVar a, Ord a) => Doc -> Function a -> Doc
ppFunc header (Function f _attrs _tvs xts t e) =
   ((header $\ ppVar f $\ fsep (map (parens . ppLocalBinder) xts) $\ (":" <+> ppType 0 t <+> "="))
     $\ ppExpr 0 e
   ) $$
   ("(*" <+> vcat [ ppVar f $\ fsep (map ppDeepPattern dps) <+> "=" $\ ppExpr 0 rhs
                  | (dps,rhs) <- patternMatchingView xts e ] <+> "*)")

ppDeepPattern :: PrettyVar a => DeepPattern a -> Doc
ppDeepPattern (DeepConPat (Global k _ _) dps) = parens (ppVar k <+> fsep (map ppDeepPattern dps))
ppDeepPattern (DeepVarPat (Local x _)) = ppVar x
ppDeepPattern (DeepLitPat lit) = ppLit lit

ppFormula :: (PrettyVar a, Ord a) => Formula a -> Int -> Doc
ppFormula Formula{..} i =
  (ppRole fm_role <+> ("x" <> int i) <+> ":") $\ (ppExpr 0 fm_body)

ppRole :: Role -> Doc
ppRole Assert = "lemma"
ppRole Prove  = "goal"

ppExpr :: (PrettyVar a, Ord a) => Int -> Expr a -> Doc
ppExpr i e | Just (c,t,f) <- ifView e = parIf (i > 0) $ "if" $\ ppExpr 0 c $\ "then" $\ ppExpr 0 t $\ "else" $\ ppExpr 0 f
ppExpr i e@(hd@(Gbl Global{..}) :@: es)
  | isNothing (makeGlobal gbl_name gbl_type (map exprType es) Nothing) =
    parIf (i > 0) $
    ppHead hd es $\ ":" $\ ppType 0 (exprType e)
ppExpr i (hd :@: es)  = parIf (i > 0 && not (null es)) $ ppHead hd es
ppExpr _ (Lcl l)      = ppVar (lcl_name l)
ppExpr i (Lam ls e)   = parIf (i > 0) $ ppQuant True "fun" ls (ppExpr 0 e)
ppExpr i (Let x b e)  = parIf (i > 0) $ sep ["let" $\ ppVar (lcl_name x) <+> "=" $\ ppExpr 0 b <+> ":" $\ ppType 0 (lcl_type x), "in" <+> ppExpr 0 e]
ppExpr i (Quant _ q ls e) = parIf (i > 0) $ ppQuant False (ppQuantName q) ls (ppExpr 0 e)
ppExpr i (Match e alts) =
  parIf (i > 0) $ block ("match" $\ ppExpr 0 e $\ "with")
                        (separating vcat (repeat "|") (map ppCase alts))
ppExpr _ LetRec{} = error "letrec not supported"

ppHead :: (PrettyVar a, Ord a) => Head a -> [Expr a] -> Doc
ppHead (Gbl gbl)   args = ppVar (gbl_name gbl) $\ fsep (map (ppExpr 1) args)
ppHead (Builtin b) [u,v] | Just d <- ppBinOp b (exprType u) = ppExpr 1 u <+> d $\ ppExpr 1 v
ppHead (Builtin At{}) args = fsep (map (ppExpr 1) args)
ppHead (Builtin b) args = ppBuiltin b $\ fsep (map (ppExpr 1) args)

ppBuiltin :: Builtin -> Doc
ppBuiltin (Lit lit) = ppLit lit
ppBuiltin IntDiv    = "div"
ppBuiltin IntMod    = "mod"
ppBuiltin Not       = "not"
ppBuiltin NumWiden  = "from_int"
ppBuiltin b         = error $ "Why3.ppBuiltin: " ++ show b

ppBinOp :: Builtin -> Type a -> Maybe Doc
ppBinOp And _     = Just "&&"
ppBinOp Or _      = Just "||"
ppBinOp Implies _ = Just "->"
ppBinOp Equal _   = Just "="
ppBinOp Distinct _= Just "<>"
ppBinOp NumAdd ty = Just (ppDotIfReal ty "+")
ppBinOp NumSub ty = Just (ppDotIfReal ty "-")
ppBinOp NumMul ty = Just (ppDotIfReal ty "*")
ppBinOp NumGt ty  = Just (ppDotIfReal ty ">")
ppBinOp NumGe ty  = Just (ppDotIfReal ty ">=")
ppBinOp NumLt ty  = Just (ppDotIfReal ty "<")
ppBinOp NumLe ty  = Just (ppDotIfReal ty "<=")
ppBinOp _ _       = Nothing

ppDotIfReal :: Type a -> Doc -> Doc
ppDotIfReal (BuiltinType Real) xs = xs <> "."
ppDotIfReal _ xs = xs

ppLit :: Lit -> Doc
ppLit (Int i)      = integer i
ppLit (Bool True)  = "true"
ppLit (Bool False) = "false"

ppQuantName :: Quant -> Doc
ppQuantName Forall = "forall"
ppQuantName Exists = "exists"

ppCase :: (PrettyVar a, Ord a) => Case a -> Doc
ppCase (Case pat rhs) = ppPat pat <+> "->" $\ ppExpr 0 rhs

ppPat :: (PrettyVar a, Ord a) => Pattern a -> Doc
ppPat pat = case pat of
  Default     -> "_"
  ConPat g ls -> ppVar (gbl_name g) $\ fsep (map (ppVar . lcl_name) ls)
  LitPat l    -> ppLit l

ppType :: (PrettyVar a, Ord a) => Int -> Type a -> Doc
ppType _ (TyVar x)     = ppTyVar x
ppType i (TyCon tc ts) = parIf (i > 0) $ ppVar tc $\ fsep (map (ppType 1) ts)
ppType i (ts :=>: r)   = parIf (i > 0) $ fsep (punctuate " ->" (map (ppType 1) (ts ++ [r])))
ppType _ (BuiltinType Integer) = "int"
ppType _ (BuiltinType Real)    = "real"
ppType _ (BuiltinType Boolean) = "bool"

ppTyVar :: (PrettyVar a, Ord a) => a -> Doc
ppTyVar x = "'" <> ppVar x

why3Keywords :: [String]
why3Keywords = words $ unlines
    [ "equal not function use import goal int"
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
    ]
