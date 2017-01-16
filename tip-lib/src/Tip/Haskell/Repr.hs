{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
-- | A representation of Haskell programs
module Tip.Haskell.Repr where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

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
  | ClassDecl [Type a] {- context -}
              (Type a) {- head -}
              [Decl a] {- declarations (type signatures) -}
  | TypeDef (Type a) (Type a)
  | Decl a `Where` [Decl a]
  | TH (Expr a)
  | Module String
  | LANGUAGE String
  | QualImport String (Maybe String)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

funDecl :: a -> [a] -> Expr a -> Decl a
funDecl f xs b = FunDecl f [(map VarPat xs,b)]

data Type a
  = TyCon a [Type a]
  | TyVar a
  | TyTup [Type a]
  | TyArr (Type a) (Type a)
  | TyForall [a] (Type a)
  | TyCtx [Type a] (Type a)
  | TyImp a (Type a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Expr a
  = Apply a [Expr a]
  | ImpVar a
  | Do [Stmt a] (Expr a)
  | Lam [Pat a] (Expr a)
  | Let a (Expr a) (Expr a)
  | ImpLet a (Expr a) (Expr a)
  | List [Expr a] -- a literal list
  | Tup [Expr a]  -- a literal tuple
  | String a      -- string from a name...
  | Noop          -- | @return ()@
  | Case (Expr a) [(Pat a,Expr a)]
  | Int Integer
  | QuoteTyCon a -- Template Haskell ''
  | QuoteName a  -- Template Haskell '
  | THSplice (Expr a) -- Template Haskell $(..)
  | Record (Expr a) [(a,Expr a)] -- record update
  | Expr a ::: Type a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

nestedTyTup :: [Type a] -> Type a
nestedTyTup []     = TyTup []
nestedTyTup (t:ts) = TyTup [t,nestedTyTup ts]

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

data Stmt a = Bind a (Expr a) | Stmt (Expr a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

