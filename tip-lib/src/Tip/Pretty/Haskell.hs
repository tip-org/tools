{-# LANGUAGE OverloadedStrings #-}
module Tip.Pretty.Haskell where

import Tip.Haskell.Repr
import Tip.Haskell.Translate
import Tip.Haskell.Rename
import qualified Tip.Core as T
import Tip.Pretty
import Tip.Fresh
import Text.PrettyPrint

ppTheory :: (Name a,PrettyVar a) => T.Theory a -> Fresh Doc
ppTheory = fmap (pp . renameDecls . addHeader . addImports) . trTheory

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
  varUnqual (Qualified _ s) = s
  varUnqual v               = varStr v

tuple ds = parens (fsep (punctuate "," ds))

instance PrettyHsVar a => Pretty (Expr a) where
  pp e =
    case e of
      Apply x [] -> ppHsVar x
      Apply x es | Lam ps b <- last es -> ((ppHsVar x $\ fsep (map pp_par (init es))) $\ "(\\" <+> fsep (map pp ps) <+> "->") $\ pp b <> ")"
      Apply x es -> ppOper x (map pp_par es)
      Do ss e    -> "do" <+> (vcat (map pp (ss ++ [Stmt e])))
      Let x e b  -> "let" <+> (ppHsVar x <+> "=" $\ pp e) $\ "in" <+> pp b
      Lam ps e   -> "\\" <+> fsep (map pp ps) <+> "->" $\ pp e
      List es    -> brackets (fsep (punctuate "," (map pp es)))
      Tup es     -> tuple (map pp es)
      String s   -> "\"" <> ppVar s <> "\""
      Case e brs -> ("case" <+> pp e <+> "of") $\ vcat [ (ppPat 0 p <+> "->") $\ pp rhs | (p,rhs) <- brs ]
      Int i      -> integer i
      QuoteTyCon tc -> "''" <> ppHsVar tc
      QuoteName x   -> "'" <> ppHsVar x
      THSplice e  -> "$" <> parens (pp e)
      Noop       -> "Prelude.return ()"
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
              fsep (punctuate " |" [ ppOper c (map (ppType 2) ts) | (c,ts) <- cons ])) $\
              (if null derivs then empty
               else "deriving" $\ tuple (map ppHsVar derivs))
        InstDecl ctx head ds ->
          (("instance" $\
            (pp_ctx ctx $\ pp head)) $\
               "where") $\ vcat (map (go 1) ds)
        TypeDef lhs rhs -> "type" <+> pp lhs <+> "=" $\ pp rhs
        decl `Where` ds -> pp decl $\ "where" $\ vcat (map pp ds)
        TH e -> pp e
        Module s -> "module" <+> text s <+> "where"
        LANGUAGE s -> "{-#" <+> "LANGUAGE" <+> text s <+> "#-}"
        QualImport s -> "import" <+> "qualified" <+> text s

instance PrettyHsVar a => Pretty (Decls a) where
  pp (Decls ds) = vcat (map pp ds)

instance PrettyHsVar a => Pretty (Type a) where
  pp = ppType 0

ppType :: PrettyHsVar a => Int -> Type a -> Doc
ppType i t0 =
  case t0 of
    TyCon t []  -> ppHsVar t
    TyCon t ts  -> parIf (i >= 2) (ppOper t (map (ppType 2) ts))
    TyVar x     -> ppHsVar x
    TyTup ts    -> tuple (map (ppType 0) ts)
    TyArr t1 t2 -> parIf (i >= 1) (ppType 1 t1 <+> "->" $\ ppType 0 t2)

