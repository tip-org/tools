{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ViewPatterns #-}
module Tip.Pretty.TFF where

import Text.PrettyPrint

import Tip.Pretty
import Tip.Pretty.Why3(Why3Var(..))
import Tip.Types
import Tip.Core hiding (apply)
import Tip.Rename
import Data.Maybe
import Data.Char (isAlphaNum)

apply :: Doc -> [Doc] -> Doc
apply s [] = s
apply s xs = cat [s <> "(", nest 2 (fsep (punctuate (text ",") xs) <> ")")]

clause :: String -> String -> Doc -> Doc
clause name kind body =
  hang ("tff(" <> text name <> ", " <> text kind <> ",") 2
       (body <> ").")

validTFFChar :: Char -> String
validTFFChar x
  | isAlphaNum x || x == '_' = [x]
  | otherwise                = ""

ppTheory :: (Ord a,PrettyVar a) => Theory a -> Doc
ppTheory (renameAvoiding [] validTFFChar . tffvarify -> Theory{..})
  = vcat
     (map ppSort thy_sorts ++
      map ppUninterp thy_sigs ++
      map ppFormula thy_asserts)

ppSort :: PrettyVar a => Sort a -> Doc
ppSort (Sort sort []) =
  clause "type" "type" $
    ppVar sort <+> ":" <+> "$tType"

ppUninterp :: PrettyVar a => Signature a -> Doc
ppUninterp (Signature f (PolyType [] arg_types result_type)) =
  clause "func" "type" $
    ppVar f <+> ":" <+>
    case arg_types of
      [] -> ppType result_type
      _  -> sep (punctuate " *" (map ppType arg_types)) <+> ">" <+> ppType result_type

ppFormula :: (Ord a, PrettyVar a) => Formula a -> Doc
ppFormula (Formula Prove _ _ [] term)  =
  clause "goal" "conjecture" (ppExpr 0 (tffify term))
ppFormula (Formula Assert _ _ [] term) =
  clause "axiom" "axiom" (ppExpr 0 (tffify term))

tffify :: Ord a => Expr a -> Expr a
tffify =
  transformExpr $ \e ->
    case e of
      Builtin Equal :@: ts ->
        ands (zipWith (===) ts (tail ts))
      Builtin And :@: es -> ands es
      Builtin Or  :@: es -> ors  es
      _ -> e

tffvarify :: Ord a => Theory a -> Theory (Why3Var a)
tffvarify = uppercase . fmap (Why3Var False)
  where
    uppercase =
      transformExprIn $ \e ->
        case e of
          Lcl lcl -> Lcl (make_upper lcl)
          Quant i q ls body -> Quant i q (map make_upper ls) body
          _ -> e
    make_upper (Local (Why3Var _ lcl_name) lcl_type) =
      Local (Why3Var True lcl_name) lcl_type

ppExpr :: (Ord a, PrettyVar a) => Int -> Expr a -> Doc
ppExpr _ (Builtin Equal :@: [t, u]) =
  hang (ppExpr 2 t <+> "=") 2 (ppExpr 2 u)
ppExpr p (Builtin Distinct :@: [t, u]) =
  hang (ppExpr 2 t <+> "!=") 2 (ppExpr 2 u)
ppExpr p (Builtin And :@: ts) =
  parIf (p > 0) $
    let u:us = punctuate " &" (map (ppExpr 1) ts) in
    sep (u:map (nest 2) us)
ppExpr p (Builtin Or :@: ts) =
  parIf (p > 0) $
    let u:us = punctuate " |" (map (ppExpr 1) ts) in
    sep (u:map (nest 2) us)
ppExpr p (Builtin Implies :@: [t, u]) =
  parIf (p > 0) $
    hang (ppExpr 1 t <+> "=>") 2 (ppExpr 1 u)
ppExpr p (Builtin Not :@: [t]) =
  parIf (p > 1) $
    "~" <> ppExpr 1 t
ppExpr _ (hd :@: ts) =
  apply (ppHead hd) (map (ppExpr 0) ts)
ppExpr _ (Lcl l) = ppVar (lcl_name l)
ppExpr _ (Quant _ q ls e) =
  hang
    (ppQuant q <> brackets (fsep (punctuate "," (map ppLocal ls))) <> ":")
    2
    (ppExpr 1 e)

ppLocal :: PrettyVar a => Local a -> Doc
ppLocal Local{..} = ppVar lcl_name <> ":" <> ppType lcl_type

ppQuant :: Quant -> Doc
ppQuant Forall = "!"
ppQuant Exists = "?"

ppHead :: PrettyVar a => Head a -> Doc
ppHead (Builtin b) = ppBuiltin b
ppHead (Gbl Global{..}) = ppVar gbl_name

ppBuiltin :: Builtin -> Doc
ppBuiltin (Lit lit) = ppLit lit
ppBuiltin Distinct  = "$distinct"
ppBuiltin IntAdd    = "$plus_int"
ppBuiltin IntSub    = "$minus_int"
ppBuiltin IntMul    = "$times_int"
ppBuiltin IntDiv    = "$div_int"
ppBuiltin IntMod    = "$mod_int"
ppBuiltin IntGt     = "$greater_int"
ppBuiltin IntGe     = "$greatereq_int"
ppBuiltin IntLt     = "$less_int"
ppBuiltin IntLe     = "$lesseq_int"

ppLit :: Lit -> Doc
ppLit (Int i)      = integer i
ppLit (Bool True)  = "$true"
ppLit (Bool False) = "$false"
ppLit (String s)   = text (show s)

ppType :: PrettyVar a => Type a -> Doc
ppType (TyVar x)        = ppVar x
ppType (TyCon tc ts)    = apply (ppVar tc) (map ppType ts)
ppType (BuiltinType bu) = ppBuiltinType bu

ppBuiltinType :: BuiltinType -> Doc
ppBuiltinType Integer = "$int"
ppBuiltinType Boolean = "$o"
