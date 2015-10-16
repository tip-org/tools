{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module Tip.QuickSpec.Translate (trProperty, backMap) where

#include "errors.h"
import Data.Map (Map)
import qualified Data.Map as M

import qualified Data.Typeable as Typeable

import qualified Data.Rewriting.Term as R

import qualified Tip.Core as Tip

import qualified QuickSpec as QS

import qualified Data.Foldable as F

import Control.Applicative

import Tip.Pretty.Haskell (varUnqual)
import Tip.Haskell.Translate (HsId(..),hsBuiltinTys,hsBuiltins,typeOfBuiltin)
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
  | Var QS.Variable
  | TyVar QS.TyVar
  deriving (Eq,Ord,Show)

instance PrettyVar a => PrettyVar (V a) where
  varStr (Orig x)  = varStr x
  varStr (Var x)   = show (QS.pretty x)
  varStr (TyVar x) = show (QS.pretty x)

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
        | Just ty <- rlookup s hsBuiltinTys -> Just (Type (\ [] -> Tip.BuiltinType ty))
        | Just bu <- rlookup s hsBuiltins   -> Just (Head [] (typeOfBuiltin bu) (\ [] -> Tip.Builtin bu))
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

trLiteral :: (Ord a,PrettyVar a) => BackMap a -> QS.Literal QS.Term -> Tip.Expr (V a)
trLiteral bm (t1 QS.:=: t2) = trTerm bm t1 Tip.=== trTerm bm t2

trTerm :: (Ord a,PrettyVar a) => BackMap a -> QS.Term -> Tip.Expr (V a)
trTerm bm tm =
  case tm of
    R.Var v -> Tip.Lcl (Tip.Local (Var v) (trType bm (QS.typ v)))
    R.Fun c (drop (QS.implicitArguments c) -> as) ->
      let name = QS.conName c
          Head tvs ty mk = FROMJUST(name) (M.lookup name bm)
      in  mk (matchTypes name tvs ty
                (trType bm (QS.typeDrop (QS.implicitArguments c) (QS.typ c))))
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

trType :: PrettyVar a => BackMap a -> QS.Type -> Tip.Type (V a)
trType bm t =
  case t of
    R.Var tv -> Tip.TyVar (TyVar tv)
    R.Fun QS.Arrow [a,b] -> trType bm a ==> trType bm b -- !! ??
    R.Fun (QS.TyCon tc) as ->
      let name = Typeable.tyConName tc
          Type mk = FROMJUST(name) (M.lookup name bm)
      in  mk (map (trType bm) as)

  where
  t ==> (ts Tip.:=>: r) = (t:ts) Tip.:=>: r
  t ==> r               = [t] Tip.:=>: r

unV :: Name a => Tip.Expr (V a) -> Fresh (Tip.Formula a)
unV e =
  do mtvs  <- freshMap [ tv | TyVar tv <- F.toList e ]
     mvars <- freshMap [ v | Var v <- F.toList e ]
     let rename (TyVar tv) = mtvs M.! tv
         rename (Var v)    = mvars M.! v
         rename (Orig f)   = f
     let e' = fmap rename e
     return $
       Tip.Formula Tip.Prove Tip.Unknown (M.elems mtvs) (Tip.mkQuant Tip.Forall (Tip.free e') e')

freshMap :: (Ord a,Name b) => [a] -> Fresh (Map a b)
freshMap xs = M.fromList <$> sequence [ (,) x <$> fresh | x <- xs ]

trProperty :: Name a => BackMap a -> QS.Prop -> Fresh (Tip.Formula a)
trProperty bm = unV . trProp bm

