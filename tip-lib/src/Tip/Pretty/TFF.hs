{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ViewPatterns #-}
module Tip.Pretty.TFF where

import Text.PrettyPrint

import Tip.Pretty
import Tip.Pretty.Why3(Why3Var(..))
import Tip.Pretty.SMT()
import Tip.Types
import Tip.Core hiding (apply)
import Tip.Rename
import Data.Char (isAlphaNum)

apply :: Doc -> [Doc] -> Doc
apply s [] = s
apply s xs = cat [s <> "(", nest 2 (fsep (punctuate (text ",") xs) <> ")")]

clause :: String -> String -> Doc -> Doc
clause name kind body =
  hang ("tff(" <> text name <> ", " <> text kind <> ",") 2
       (body <> ").")

validTFFChar :: Char -> Bool
validTFFChar x = isAlphaNum x || x == '_'

ppTheory :: (Ord a,PrettyVar a) => Theory a -> Doc
ppTheory (renameAvoiding [] (filter validTFFChar) . tffvarify -> Theory{..})
  = vcat
     (map ppSort thy_sorts ++
      map ppUninterp thy_sigs ++
      map ppFormula thy_asserts)

ppSort :: PrettyVar a => Sort a -> Doc
ppSort (Sort sort _ []) =
  clause "type" "type" $
    ppVar sort <+> ":" <+> "$tType"
ppSort _ = error "polymorphism not supported in TFF"

ppUninterp :: PrettyVar a => Signature a -> Doc
ppUninterp (Signature f _ (PolyType [] arg_types result_type)) =
  clause "func" "type" $
    ppVar f <+> ":" <+>
    case arg_types of
      [] -> ppType result_type
      _  -> sep (punctuate " *" (map ppType arg_types)) <+> ">" <+> ppType result_type
ppUninterp _ = error "polymorphism not supported in TFF"

ppFormula :: (Ord a, PrettyVar a) => Formula a -> Doc
ppFormula form =
  case fm_role form of
    Prove -> clause "goal" "conjecture" body
    Assert -> clause "axiom" "axiom" body
  where
    body = ppExpr 0 (tffify (fm_body form))

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
ppExpr _ (Builtin Equal :@: [t, u])
  | exprType t == BuiltinType Boolean =
    hang (ppExpr 2 t <+> "<=>") 2 (ppExpr 2 u)
  | otherwise =
    hang (ppExpr 2 t <+> "=") 2 (ppExpr 2 u)
ppExpr p (Builtin Distinct :@: [t, u])
  | exprType t == BuiltinType Boolean =
    hang (ppExpr 2 t <+> "<~>") 2 (ppExpr 2 u)
  | otherwise =
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
ppExpr p e
  | Just (b, t, e) <- ifView e =
    ppExpr p ((b ==> t) /\ (neg b ==> e))
ppExpr _ e = error ("unsupported expression in TFF: " ++ show (pp e))

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
ppBuiltin NumAdd    = "$sum"
ppBuiltin NumSub    = "$difference"
ppBuiltin NumMul    = "$product"
ppBuiltin NumDiv    = "$quotient"
ppBuiltin IntDiv    = "$quotient_e"
ppBuiltin IntMod    = "$remainder_e"
ppBuiltin NumGt     = "$greater"
ppBuiltin NumGe     = "$greatereq"
ppBuiltin NumLt     = "$less"
ppBuiltin NumLe     = "$lesseq"
ppBuiltin NumWiden  = "$to_real"
ppBuiltin _         = error "unsupported builtin in TFF"

ppLit :: Lit -> Doc
ppLit (Int i)      = integer i
ppLit (Bool True)  = "$true"
ppLit (Bool False) = "$false"

ppType :: PrettyVar a => Type a -> Doc
ppType (TyVar x)        = ppVar x
ppType (TyCon tc ts)    = apply (ppVar tc) (map ppType ts)
ppType (BuiltinType bu) = ppBuiltinType bu
ppType (_ :=>: _)       = error "lambda functions not supported in TFF"

ppBuiltinType :: BuiltinType -> Doc
ppBuiltinType Integer = "$int"
ppBuiltinType Real    = "$real"
ppBuiltinType Boolean = "$o"
