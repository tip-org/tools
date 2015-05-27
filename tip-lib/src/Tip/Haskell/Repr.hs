{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
-- | A representation of Haskell programs
module Tip.Haskell.Repr where

import Text.PrettyPrint
import Tip.Pretty
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

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
class PrettyVar a => HsVar a where
  varUnqual :: a -> String

ppUnqual :: HsVar a => a -> Doc
ppUnqual = text . varUnqual

data Decls a = Decls [Decl a]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Decl a
  = TySig a
          [Type a] {- class contexts -}
          (Type a)
  | FunDecl a [([Pat a],Expr a)]
  | DataDecl a               {- type constructor name -}
             [a]             {- type variables -}
             [(a,[Type a])]  {- constructors -}
             [a]             {- instance derivings -}
  | InstDecl [Type a] {- context -}
             (Type a) {- head -}
             [Decl a] {- declarations (associated types and fun decls) -}
  | TypeDef (Type a) (Type a)
  | Decl a `Where` [Decl a]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

funDecl :: a -> [a] -> Expr a -> Decl a
funDecl f xs b = FunDecl f [(map VarPat xs,b)]

data Type a
  = TyCon a [Type a]
  | TyVar a
  | TyTup [Type a]
  | TyArr (Type a) (Type a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

modTyCon :: (a -> a) -> Type a -> Type a
modTyCon f t0 =
  case t0 of
    TyCon t ts  -> TyCon (f t) (map (modTyCon f) ts)
    TyVar x     -> TyVar x
    TyTup ts    -> TyTup (map (modTyCon f) ts)
    TyArr t1 t2 -> TyArr (modTyCon f t1) (modTyCon f t2)

data Expr a
  = Apply a [Expr a]
  | Do [Stmt a] (Expr a)
  | Lam [Pat a] (Expr a)
  | Let a (Expr a) (Expr a)
  | List [Expr a] -- a literal list
  | Tup [Expr a]  -- a literal tuple
  | String a      -- string from a name...
  | Noop          -- | @return ()@
  | Case (Expr a) [(Pat a,Expr a)]
  | Int Integer
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

nestedTup :: [Expr a] -> Expr a
nestedTup [] = Tup []
nestedTup (d:ds) = Tup [d,nestedTup ds]

nestedTupPat :: [Pat a] -> Pat a
nestedTupPat []     = TupPat []
nestedTupPat (d:ds) = TupPat [d,nestedTupPat ds]

mkDo []      x = x
mkDo ss1 (Do ss2 e) = mkDo (ss1 ++ ss2) e
mkDo ss Noop = case (init ss,last ss) of
  (i,Stmt e)   -> mkDo i e
  (i,Bind x e) -> mkDo i e
mkDo ss e = Do ss e

var :: a -> Expr a
var x = Apply x []

data Pat a = VarPat a | ConPat a [Pat a] | TupPat [Pat a] | WildPat | IntPat Integer
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Stmt a = Bind a (Expr a) | BindTyped a (Type a) (Expr a) | Stmt (Expr a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

tuple ds = parens (fsep (punctuate "," ds))

instance HsVar a => Pretty (Expr a) where
  pp e =
    case e of
      Apply x [] -> ppVar x
      Apply x es | Lam ps b <- last es -> ((ppVar x $\ fsep (map pp_par (init es))) $\ "(\\" <+> fsep (map pp ps) <+> "->") $\ pp b <> ")"
      Apply x es -> ppVar x $\ fsep (map pp_par es)
      Do ss e    -> "do" <+> (vcat (map pp (ss ++ [Stmt e])))
      Let x e b  -> "let" <+> (ppVar x <+> "=" $\ pp e) $\ "in" <+> pp b
      Lam ps e   -> "\\" <+> fsep (map pp ps) <+> "->" $\ pp e
      List es    -> brackets (fsep (punctuate "," (map pp es)))
      Tup es     -> tuple (map pp es)
      String s   -> "\"" <> ppVar s <> "\""
      Case e brs -> ("case" <+> pp e <+> "of") $\ vcat [ (ppPat 0 p <+> "->") $\ pp rhs | (p,rhs) <- brs ]
      Int i      -> integer i
      Noop       -> "Prelude.return ()"
   where
    pp_par e0 =
      case e0 of
        Apply x []  -> pp e0
        List{}      -> pp e0
        Tup{}       -> pp e0
        String{}    -> pp e0
        _           -> parens (pp e0)

instance HsVar a => Pretty (Stmt a) where
  pp (Bind x e)        = ppVar x <+> "<-" $\ pp e
  pp (BindTyped x t e) = (ppVar x <+> "::" $\ pp t <+> "<-") $\ pp e
  pp (Stmt e)          = pp e

instance HsVar a => Pretty (Pat a) where
  pp = ppPat 0

ppPat :: HsVar a => Int -> Pat a -> Doc
ppPat i p =
  case p of
    VarPat x    -> ppVar x
    ConPat k [] -> ppVar k
    ConPat k ps -> parIf (i >= 1) (ppVar k $\ fsep (map (ppPat 1) ps))
    TupPat ps   -> tuple (map (ppPat 0) ps)
    WildPat     -> "_"

instance HsVar a => Pretty (Decl a) where
  pp = go 0
    where
    pp_ctx [] = empty
    pp_ctx ctx = pp (TyTup ctx) <+> "=>"
    go i d =
      case d of
        TySig f ctx t -> (ppVar f <+> "::" $\ pp_ctx ctx) $\ pp t
        FunDecl f xs ->
          vcat
            [ ((if i == 0 then ppVar else ppUnqual) f $\ fsep (map (ppPat 1) ps) <+> "=") $\ pp b
            | (ps,b) <- xs
            ]
        DataDecl tc tvs cons derivs ->
          ((((case cons of
               [(_,[_])] -> "newtype"
               _         -> "data") $\ ppVar tc) $\ fsep (map ppVar tvs) <+> "=") $\
            fsep (punctuate " |" [ ppCon c ts | (c,ts) <- cons ])) $\
            (if null derivs then empty
             else "deriving" <+> parens (fsep (punctuate "," (map ppVar derivs))))
        InstDecl ctx head ds ->
          (("instance" $\
            (pp_ctx ctx $\ pp head)) $\
               "where") $\ vcat (map (go 1) ds)
        TypeDef lhs rhs -> "type" <+> pp lhs <+> "=" $\ pp rhs
        decl `Where` ds -> pp decl $\ "where" $\ vcat (map pp ds)

ppCon :: HsVar a => a -> [Type a] -> Doc
ppCon c ts = case varStr c of
  '(':':':xs | [t1,t2] <- ts -> ppType 2 t1 <+> (":" <> text (init xs)) $\ ppType 2 t2
  _                          -> ppVar c $\ fsep (map (ppType 2) ts)

instance HsVar a => Pretty (Decls a) where
  pp (Decls ds) = vcat (map pp ds)

instance HsVar a => Pretty (Type a) where
  pp = ppType 0

ppType :: HsVar a => Int -> Type a -> Doc
ppType i t0 =
  case t0 of
    TyCon t []  -> ppVar t
    TyCon t ts  -> parIf (i >= 2) (ppVar t $\ fsep (map (ppType 2) ts))
    TyVar x     -> ppVar x
    TyTup ts    -> tuple (map (ppType 0) ts)
    TyArr t1 t2 -> parIf (i >= 1) (ppType 1 t1 <+> "->" $\ ppType 0 t2)

