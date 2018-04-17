{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module Tip.QuickSpec.Translate (trProperty, backMap, BackMap, BackEntry(..)) where

#include "errors.h"
import Data.Map (Map)
import qualified Data.Map as M

import qualified Data.Typeable as Typeable

import qualified Tip.Core as Tip

import qualified QuickSpec.Type as QS
import qualified QuickSpec.Prop as QS
import qualified QuickSpec.Term as QS
import qualified QuickSpec.Haskell as QS
import qualified QuickSpec.Explore.PartialApplication as QS
import qualified Twee.Base as Twee

import qualified Data.Foldable as F

import Tip.Pretty.Haskell (varUnqual)
import Tip.Haskell.Translate (HsId(..),hsBuiltinTys,hsBuiltins,prelude,ratio,typesOfBuiltin)
import Tip.Haskell.Rename (RenameMap)

import Tip.Scope
import Tip.Fresh

import Tip.Pretty (PrettyVar(..), pp)
import Tip.Pretty.SMT ()

import Data.Maybe

type Term = QS.Term (QS.PartiallyApplied QS.Constant)

data BackEntry a
  = Head
      { head_tvs  :: [a]
      , head_type :: Tip.Type a
      , head_make :: [Tip.Type a] -> Tip.Head a
      }
  | Type
      { type_make :: [Tip.Type a] -> Tip.Type a
      }

type BackMap a = Map String (BackEntry (V a))

data V a
  = Orig a
  | Var QS.Var
  | Eta Int Int
  | TyVar Twee.Var
  deriving (Eq,Ord,Show)

instance PrettyVar a => PrettyVar (V a) where
  varStr (Orig x)  = varStr x
  varStr (Var x) = Twee.prettyShow x
  varStr (Eta _ _) = "x"
  varStr (TyVar x) = Twee.prettyShow x

rlookup :: Eq b => b -> [(a,b)] -> Maybe a
rlookup x = lookup x . map (\(x,y) -> (y,x))

backMap :: forall a . (Ord a,PrettyVar a) => Tip.Theory a -> RenameMap a -> BackMap a
backMap thy rm =
    M.fromList $ catMaybes [ fmap ((,) (varUnqual str)) (back_entry orig)
                           | (orig,str) <- M.toList rm ]
  where
  back_entry :: HsId a -> Maybe (BackEntry (V a))
  back_entry i =
    case i of
      Exact s
        | [(x,"")] <- reads s -> Just (Head __ __ (\ _ -> Tip.Builtin (Tip.Lit (Tip.Int x))))

      Qualified "Prelude" _ "id" -> Just (Head __ __ (\ _ -> Tip.Builtin Tip.At))
      Qualified "Prelude" _ s
        | Just ty <- rlookup (prelude s :: HsId ()) hsBuiltinTys -> Just (Type (\ [] -> Tip.BuiltinType ty))
        | Just ty <- rlookup (ratio s :: HsId ()) hsBuiltinTys -> Just (Type (\ [] -> Tip.BuiltinType ty))
        | Just bu <- rlookup s hsBuiltins   -> Just (Head __ __ (\ _ -> Tip.Builtin bu))
        | [(b,"")] <- reads s               -> Just (Head __ __ (\ _ -> Tip.Builtin (Tip.Lit (Tip.Bool b))))

      Other f
        | Just g <- lookupGlobal f scp
        , case g of
            FunctionInfo{}    -> True
            ConstructorInfo{} -> True
            _                 -> False
        , let pt@(Tip.PolyType tvs args res) = globalType g
        -> Just (Head (map Orig tvs)
                      (fmap Orig (args ==> res))
                      (Tip.Gbl . Tip.Global (Orig f) (fmap Orig pt)))

        | Just dt <- lookupDatatype f scp
        -> Just (Type (Tip.TyCon (Orig (Tip.data_name dt))))

      _ -> Nothing

  scp = scope thy

  [] ==> r = r
  as ==> r = as Tip.:=>: r

trProp :: (Ord a,PrettyVar a) => BackMap a -> QS.Prop Term -> Tip.Expr (V a)
trProp bm (assums QS.:=>: goal) = map (trEquation bm) assums Tip.===> trEquation bm goal

trEquation :: (Ord a,PrettyVar a) => BackMap a -> QS.Equation Term -> Tip.Expr (V a)
trEquation bm (t1 QS.:=: t2) = trTerm 0 bm t1 Tip.=== trTerm 0 bm t2

trTerm :: (Ord a,PrettyVar a) => Int -> BackMap a -> Term -> Tip.Expr (V a)
trTerm d bm tm =
  case tm of
    QS.Var v ->
      Tip.Lcl (Tip.Local (Var v) (trType Inner bm (QS.typ v)))
    QS.App (QS.Apply _) [t, u] ->
      Tip.Builtin Tip.At Tip.:@: [trTerm (d+1) bm t, trTerm (d+1) bm u]
    QS.App (QS.Partial c _) as ->
      let name = QS.con_name c
          Head tvs ty mk = FROMJUST(name) (M.lookup name bm)
          nargs = QS.typeArity (QS.typ c)
          hd = mk (matchTypes name tvs ty (trType Outer bm (QS.typ c)))
          missing = drop (length as) (headArgs hd)
          lcls = [Tip.Local (Eta d n) ty | (n, ty) <- zip [0..] missing]

      in
        (if null lcls then id else Tip.Lam lcls) $
        hd Tip.:@: (map (trTerm (d+1) bm) as ++ map Tip.Lcl lcls)

matchTypes :: (Ord a,PrettyVar a) => String -> [a] -> Tip.Type a -> Tip.Type a -> [Tip.Type a]
matchTypes name tvs tmpl ty =
  case Tip.matchTypesIn tvs [(tmpl,ty)] of
    Just ts -> ts
    Nothing ->
      ERROR(name ++ ": cannot match types"
            ++ "\n" ++ show (map varStr tvs)
            ++ "\n" ++ show (pp tmpl)
            ++ "\n" ++ show (pp ty))

headArgs :: Ord a => Tip.Head a -> [Tip.Type a]
headArgs (Tip.Builtin b) =
  case head (typesOfBuiltin b) of
    args Tip.:=>: _ -> args
    _ -> []
headArgs (Tip.Gbl g) = fst (Tip.gblType g)

data Mode = Outer | Inner deriving Eq

trType :: PrettyVar a => Mode -> BackMap a -> QS.Type -> Tip.Type (V a)
trType mode bm t =
  case t of
    Twee.Var tv -> Tip.TyVar (TyVar tv)
    Twee.App (Twee.F QS.Arrow) (Twee.Cons a (Twee.Cons b Twee.Empty)) ->
      trType Inner bm a ==> trType mode bm b -- !! ??
    Twee.App (Twee.F (QS.TyCon tc)) as ->
      let name = Typeable.tyConName tc
          Type mk = FROMJUST(name) (M.lookup name bm)
      in  mk (map (trType Inner bm) (Twee.unpack as))

  where
  t ==> (ts Tip.:=>: r)
    | mode == Outer = (t:ts) Tip.:=>: r
  t ==> r = [t] Tip.:=>: r

unV :: Name a => Tip.Expr (V a) -> Fresh (Tip.Formula a)
unV e =
  do mtvs  <- freshMap [ tv | TyVar tv <- F.toList e ]
     mvars <- freshMap [ v | Var v <- F.toList e ]
     metas <- freshMap [ (m, n) | Eta m n <- F.toList e ]
     let rename (TyVar tv) = mtvs M.! tv
         rename (Var v) = mvars M.! v
         rename (Eta m n)  = metas M.! (m, n)
         rename (Orig f)   = f
     let e' = fmap rename e
     return $
       Tip.putAttr Tip.lemma () $
       Tip.Formula Tip.Prove [] (M.elems mtvs) (Tip.mkQuant Tip.Forall (Tip.free e') e')

freshMap :: (Ord a,Name b) => [a] -> Fresh (Map a b)
freshMap xs = M.fromList <$> sequence [ (,) x <$> fresh | x <- xs ]

trProperty :: Name a => BackMap a -> QS.Prop Term -> Fresh (Tip.Formula a)
trProperty bm = unV . trProp bm

