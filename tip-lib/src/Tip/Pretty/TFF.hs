{-# LANGUAGE RecordWildCards, OverloadedStrings, PatternGuards, ViewPatterns #-}
module Tip.Pretty.TFF where

import Text.PrettyPrint hiding (Mode)

import Prelude hiding ((<>))
import Tip.Pretty
import Tip.Pretty.Why3(Why3Var(..))
import Tip.Pretty.SMT()
import Tip.Types
import Tip.Core hiding (apply)
import Tip.Rename
import Data.Char (isAlphaNum)

data Mode = Typed | Untyped deriving Eq

apply :: Doc -> [Doc] -> Doc
apply s [] = s
apply s xs = cat [s <> "(", nest 2 (fsep (punctuate (text ",") xs) <> ")")]

clause :: Mode -> String -> String -> Doc -> Doc
clause mode name kind body =
  hang (text modeStr <> text "(" <> text name <> ", " <> text kind <> ",") 2
       (body <> ").")
  where
    modeStr =
      case mode of
        Typed -> "tff"
        Untyped -> "fof"

validTFFChar :: Char -> Bool
validTFFChar x = isAlphaNum x || x == '_'

ppTheory :: (Ord a,PrettyVar a) => Mode -> Theory a -> Doc
ppTheory mode (renameAvoiding [] (filter validTFFChar) . tffvarify -> Theory{..})
  = vcat
     (map (ppSort mode) thy_sorts ++
      map (ppUninterp mode) thy_sigs ++
      map (ppFormula mode) thy_asserts)

ppSort :: PrettyVar a => Mode -> Sort a -> Doc
ppSort Untyped _ = empty
ppSort mode (Sort sort _ []) =
  clause mode "type" "type" $
    ppVar sort <+> ":" <+> "$tType"
ppSort _ _ = error "polymorphism not supported in TFF"

ppUninterp :: PrettyVar a => Mode -> Signature a -> Doc
ppUninterp Untyped _ = empty
ppUninterp mode (Signature f _ (PolyType [] arg_types result_type)) =
  clause mode "func" "type" $
    ppVar f <+> ":" <+>
    case arg_types of
      [] -> ppType result_type
      _  -> sep (punctuate " *" (map ppType arg_types)) <+> ">" <+> ppType result_type
ppUninterp _ _ = error "polymorphism not supported in TFF"

ppFormula :: (Ord a, PrettyVar a) => Mode -> Formula a -> Doc
ppFormula mode form =
  case fm_role form of
    Prove -> clause mode "goal" "conjecture" body
    Assert -> clause mode "axiom" "axiom" body
  where
    body = ppExpr mode 0 (tffify (fm_body form))

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

ppExpr :: (Ord a, PrettyVar a) => Mode -> Int -> Expr a -> Doc
ppExpr mode p (Builtin Equal :@: [t, u])
  | exprType t == BuiltinType Boolean =
    parIf (p > 0) $ hang (ppExpr mode 2 t <+> "<=>") 2 (ppExpr mode 2 u)
  | otherwise =
    hang (ppExpr mode 2 t <+> "=") 2 (ppExpr mode 2 u)
ppExpr mode p (Builtin Distinct :@: [t, u])
  | exprType t == BuiltinType Boolean =
    parIf (p > 0) $ hang (ppExpr mode 2 t <+> "<~>") 2 (ppExpr mode 2 u)
  | otherwise =
    hang (ppExpr mode 2 t <+> "!=") 2 (ppExpr mode 2 u)
ppExpr mode p (Builtin And :@: ts) =
  parIf (p > 0) $
    let u:us = punctuate " &" (map (ppExpr mode 1) ts) in
    sep (u:map (nest 2) us)
ppExpr mode p (Builtin Or :@: ts) =
  parIf (p > 0) $
    let u:us = punctuate " |" (map (ppExpr mode 1) ts) in
    sep (u:map (nest 2) us)
ppExpr mode p (Builtin Implies :@: [t, u]) =
  parIf (p > 0) $
    hang (ppExpr mode 1 t <+> "=>") 2 (ppExpr mode 1 u)
ppExpr mode p (Builtin Not :@: [t]) =
  parIf (p > 1) $
    "~" <> ppExpr mode 1 t
ppExpr mode _ (hd :@: ts) =
  apply (ppHead hd) (map (ppExpr mode 0) ts)
ppExpr _ _ (Lcl l) = ppVar (lcl_name l)
ppExpr mode p (Quant _ _ [] e) =
  ppExpr mode p e
ppExpr mode _ (Quant _ q ls e) =
  hang
    (ppQuant q <> brackets (fsep (punctuate "," (map (ppLocal mode) ls))) <> ":")
    2
    (ppExpr mode 1 e)
ppExpr mode p e
  | Just (b, t, e) <- ifView e =
    if exprType e == boolType then
      ppExpr mode p ((b ==> t) /\ (neg b ==> e))
    else
      apply (text "$ite") (map (ppExpr mode 0) [b, t, e])
ppExpr _ _ e = error ("unsupported expression in TFF: " ++ show (pp e))

ppLocal :: PrettyVar a => Mode -> Local a -> Doc
ppLocal Typed Local{..} = ppVar lcl_name <> ":" <> ppType lcl_type
ppLocal Untyped Local{..} = ppVar lcl_name

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
