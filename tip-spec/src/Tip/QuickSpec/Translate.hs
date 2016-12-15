{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module Tip.QuickSpec.Translate (trProperty, backMap) where

#include "errors.h"
import Data.Map (Map)
import qualified Data.Map as M

import qualified Data.Typeable as Typeable

import qualified Tip.Core as Tip

import qualified QuickSpec as QS
import qualified Twee.Base as Twee

import qualified Data.Foldable as F

import Control.Applicative

import Tip.Pretty.Haskell (varUnqual)
import Tip.Haskell.Translate (HsId(..),hsBuiltinTys,hsBuiltins,prelude,ratio)
import Tip.Haskell.Rename (RenameMap)

import Tip.Scope
import Tip.Fresh

import Tip.Pretty (PrettyVar(..), pp)
import Tip.Pretty.SMT ()

import Data.Maybe

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
  | Var QS.Type Twee.Var
  | TyVar Twee.Var
  deriving (Eq,Ord,Show)

instance PrettyVar a => PrettyVar (V a) where
  varStr (Orig x)  = varStr x
  varStr (Var _ x) = Twee.prettyShow x
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

trProp :: (Ord a,PrettyVar a) => BackMap a -> QS.Prop -> Tip.Expr (V a)
trProp bm (assums QS.:=>: goal) = map (trLiteral bm) assums Tip.===> trLiteral bm goal

trLiteral :: (Ord a,PrettyVar a) => BackMap a -> QS.Literal (Twee.Term QS.Constant) -> Tip.Expr (V a)
trLiteral bm (t1 QS.:=: t2) = trTerm bm t1 Tip.=== trTerm bm t2

trTerm :: (Ord a,PrettyVar a) => BackMap a -> Twee.Term QS.Constant -> Tip.Expr (V a)
trTerm bm tm =
  case tm of
    Twee.App (QS.Id ty) [Twee.Var v] ->
      Tip.Lcl (Tip.Local (Var ty v) (trType Inner bm ty))
    Twee.App (QS.Apply ty) [t, u] ->
      Tip.Builtin Tip.At Tip.:@: [trTerm bm t, trTerm bm u]
    Twee.App c (drop (QS.implicitArity (QS.typ (QS.conGeneralValue c))) -> as) ->
      let name = QS.conName c
          Head tvs ty mk = FROMJUST(name) (M.lookup name bm)
      in  mk (matchTypes name tvs ty
                (trType Outer bm (QS.typeDrop (QS.implicitArity (QS.typ (QS.conGeneralValue c))) (QS.typ c))))
            Tip.:@: map (trTerm bm) as

matchTypes :: (Ord a,PrettyVar a) => String -> [a] -> Tip.Type a -> Tip.Type a -> [Tip.Type a]
matchTypes name tvs tmpl ty =
  case Tip.matchTypesIn tvs [(tmpl,ty)] of
    Just ts -> ts
    Nothing ->
      ERROR(name ++ ": cannot match types"
            ++ "\n" ++ show (map varStr tvs)
            ++ "\n" ++ show (pp tmpl)
            ++ "\n" ++ show (pp ty))

data Mode = Outer | Inner deriving Eq

trType :: PrettyVar a => Mode -> BackMap a -> QS.Type -> Tip.Type (V a)
trType mode bm t =
  case t of
    Twee.Var tv -> Tip.TyVar (TyVar tv)
    Twee.App QS.Arrow [a,b] -> trType Inner bm a ==> trType mode bm b -- !! ??
    Twee.App (QS.TyCon tc) as ->
      let name = Typeable.tyConName tc
          Type mk = FROMJUST(name) (M.lookup name bm)
      in  mk (map (trType Inner bm) as)

  where
  t ==> (ts Tip.:=>: r)
    | mode == Outer = (t:ts) Tip.:=>: r
  t ==> r = [t] Tip.:=>: r

unV :: Name a => Tip.Expr (V a) -> Fresh (Tip.Formula a)
unV e =
  do mtvs  <- freshMap [ tv | TyVar tv <- F.toList e ]
     mvars <- freshMap [ (ty, v) | Var ty v <- F.toList e ]
     let rename (TyVar tv) = mtvs M.! tv
         rename (Var ty v)    = mvars M.! (ty, v)
         rename (Orig f)   = f
     let e' = fmap rename e
     return $
       Tip.putAttr Tip.speculatedLemma () $
       Tip.Formula Tip.Prove [] (M.elems mtvs) (Tip.mkQuant Tip.Forall (Tip.free e') e')

freshMap :: (Ord a,Name b) => [a] -> Fresh (Map a b)
freshMap xs = M.fromList <$> sequence [ (,) x <$> fresh | x <- xs ]

trProperty :: Name a => BackMap a -> QS.Prop -> Fresh (Tip.Formula a)
trProperty bm = unV . trProp bm

