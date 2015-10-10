{-# LANGUAGE OverloadedStrings #-}
module Tip.Pretty.Haskell (module Tip.Pretty.Haskell, RenameMap, Mode(..)) where

import Tip.Haskell.Repr
import Tip.Haskell.Translate
import Tip.Haskell.Rename
import qualified Tip.Core as T
import Tip.Pretty
import Tip.Fresh
import Text.PrettyPrint hiding (Mode)

import Data.Map (Map)

ppTheory :: Name a => Mode -> T.Theory a -> Doc
ppTheory mode = fst . ppTheoryWithRenamings mod_name mode
  where
  mod_name =
    case mode of
      Feat{}           -> "Main"
      LazySmallCheck{} -> "Main"
      Smten{}          -> "Main"
      _                -> "A"

ppTheoryWithRenamings :: Name a => String -> Mode -> T.Theory a -> (Doc,RenameMap a)
ppTheoryWithRenamings mod_name mode = fst_pp . renameDecls . addHeader mod_name . addImports . trTheory mode
  where fst_pp (x,y) = (pp x,y)

-- * Pretty printing

-- | In instance declarations, you cannot write qualified variables,
--   but need to write them unqualified. As an example, the mempty part
--   here is incorrect:
--
-- @
-- instance Data.Monoid.Monoid T where
--   Data.Monoid.mempty = K
-- @
--
-- Thus, instance function declarations will be pretty printed with ppUnqual.
class PrettyVar a => PrettyHsVar a where
  varUnqual :: a -> String

ppUnqual :: PrettyHsVar a => a -> Doc
ppUnqual = text . varUnqual

ppHsVar :: PrettyHsVar a => a -> Doc
ppHsVar x = parIf (isOp x) (ppVar x)

ppOperQ :: PrettyHsVar a => Bool -> a -> [Doc] -> Doc
ppOperQ qual x ds =
  case ds of
    d1:d2:ds | isOp x -> parIf (not (null ds)) (d1 <+> pp_x $\ d2) $\ fsep ds
    _ -> parIf (isOp x) (pp_x $\ fsep ds)
  where
  pp_x | qual = ppVar x
       | otherwise = ppUnqual x

ppOper :: PrettyHsVar a => a -> [Doc] -> Doc
ppOper = ppOperQ True

isOp :: PrettyHsVar a => a -> Bool
isOp = isOperator . varUnqual

instance PrettyVar a => PrettyHsVar (HsId a) where
  varUnqual (Qualified _ _ s) = s
  varUnqual v                 = varStr v

tuple ds = parens (fsep (punctuate "," ds))

csv = sep . punctuate ","

instance PrettyHsVar a => Pretty (Expr a) where
  pp e =
    case e of
      Apply x [] -> ppHsVar x
      Apply x es | Lam ps b <- last es -> ((ppHsVar x $\ fsep (map pp_par (init es))) $\ "(\\" <+> fsep (map (ppPat 1) ps) <+> "->") $\ pp b <> ")"
      Apply x es -> ppOper x (map pp_par es)
      ImpVar x   -> "?" <> ppHsVar x
      Do ss e    -> "do" <+> (vcat (map pp (ss ++ [Stmt e])))
      Let x e b  -> "let" <+> (ppHsVar x <+> "=" $\ pp e) $\ "in" <+> pp b
      ImpLet x e b  -> "let" <+> ("?" <> ppHsVar x <+> "=" $\ pp e) $\ "in" <+> pp b
      Lam ps e   -> "\\" <+> fsep (map pp ps) <+> "->" $\ pp e
      List es    -> brackets (csv (map pp es))
      Tup es     -> tuple (map pp es)
      String s   -> "\"" <> ppUnqual s <> "\""
      Case e brs -> ("case" <+> pp e <+> "of") $\ vcat [ (ppPat 0 p <+> "->") $\ pp rhs | (p,rhs) <- brs ]
      Int i      -> integer i
      Noop       -> "Prelude.return ()"
      QuoteTyCon tc -> "''" <> ppHsVar tc
      QuoteName x   -> "'" <> ppHsVar x
      THSplice e    -> "$" <> parens (pp e)
      Record e upd  -> pp_par e $\ braces (sep (punctuate "," [ ppHsVar f <+> "=" $\ pp rhs | (f,rhs) <- upd ]))
      e ::: t       -> pp_par e <+> "::" $\ pp t
   where
    pp_par e0 =
      case e0 of
        Apply x []  -> pp e0
        List{}      -> pp e0
        Tup{}       -> pp e0
        String{}    -> pp e0
        _           -> parens (pp e0)

instance PrettyHsVar a => Pretty (Stmt a) where
  pp (Bind x e)        = ppHsVar x <+> "<-" $\ pp e
  pp (BindTyped x t e) = (ppHsVar x <+> "::" $\ pp t <+> "<-") $\ pp e
  pp (Stmt e)          = pp e

instance PrettyHsVar a => Pretty (Pat a) where
  pp = ppPat 0

ppPat :: PrettyHsVar a => Int -> Pat a -> Doc
ppPat i p =
  case p of
    VarPat x    -> ppHsVar x
    ConPat k [] -> ppHsVar k
    ConPat k ps -> parIf (i >= 1) (ppOper k (map (ppPat 1) ps))
    TupPat ps   -> tuple (map (ppPat 0) ps)
    IntPat i    -> integer i
    WildPat     -> "_"

instance PrettyHsVar a => Pretty (Decl a) where
  pp = go 0
    where
    pp_ctx [] = empty
    pp_ctx ctx = pp (TyTup ctx) <+> "=>"
    go i d =
      case d of
        TySig f ctx t -> (ppHsVar f <+> "::" $\ pp_ctx ctx) $\ pp t
        FunDecl f xs ->
          vcat
            [ (ppOperQ (i == 0) f (map (ppPat 1) ps) <+> "=") $\ pp b
            | (ps,b) <- xs
            ]
        DataDecl tc tvs cons derivs ->
          let dat = case cons of
               [(_,[_])] -> "newtype"
               _         -> "data"
          in ((dat $\ ppOper tc (map ppHsVar tvs) <+> "=") $\
              fsep (punctuate " |" [ ppOper c (map (ppType True 2) ts) | (c,ts) <- cons ])) $\
              (if null derivs then empty
               else "deriving" $\ tuple (map ppHsVar derivs))
        InstDecl ctx head ds ->
          (("instance" $\
            (pp_ctx ctx $\ pp head)) $\
               "where") $\ vcat (map (go 1) ds)
        ClassDecl ctx head ds ->
          (("class" $\
            (pp_ctx ctx $\ pp head)) $\
               "where") $\ vcat (map (go 1) ds)
        TypeDef lhs rhs -> "type" <+> ppType False 0 lhs <+> "=" $\ pp rhs
        decl `Where` ds -> go i decl $\ "where" $\ vcat (map (go 1) ds)
        TH e -> pp e
        Module s -> "module" <+> text s <+> "where"
        LANGUAGE s -> "{-#" <+> "LANGUAGE" <+> text s <+> "#-}"
        QualImport m ms -> "import" <+> "qualified" <+> text m $\
                             case ms of
                                Nothing -> empty
                                Just s  -> "as" <+> text s

instance PrettyHsVar a => Pretty (Decls a) where
  pp (Decls ds) = vcat (map pp ds)

instance PrettyHsVar a => Pretty (Type a) where
  pp = ppType True 0

ppType :: PrettyHsVar a => Bool -> Int -> Type a -> Doc
ppType qual i t0 =
  case t0 of
    TyCon t []  -> ppHsVar t
    TyCon t ts  -> parIf (i >= 2) (ppOperQ qual t (map (ppType True 2) ts))
    TyVar x     -> ppHsVar x
    TyTup ts    -> tuple (map (ppType True 0) ts)
    TyArr t1 t2 -> parIf (i >= 1) (ppType True 1 t1 <+> "->" $\ ppType True 0 t2)
    TyCtx ctx t -> parIf (i >= 1) (pp (TyTup ctx) <+> "=>" $\ ppType qual 0 t)
    TyForall tvs t  -> parIf (i >= 1) ("forall" <+> fsep (map ppVar tvs) <+> "." $\ ppType qual 0 t)
    TyImp x t       -> parIf (i >= 1) ("?" <> ppVar x <+> "::" $\ ppType qual 0 t)

