{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.AxiomatizeFuncdefs where

#include "errors.h"
import Tip.Core
import Tip.Fresh
import Tip.Scope

import Data.Maybe
import Data.List (delete)
import Data.Generics.Geniplate
import Control.Applicative

-- | Transforms define-fun to declare-fun in the most straightforward way.
--   All parts of the right hand side is preserved, including match and if-then-else.
axiomatizeFuncdefs :: Theory a -> Theory a
axiomatizeFuncdefs thy@Theory{..} =
  thy{
    thy_funcs   = [],
    thy_sigs    = thy_sigs ++ abs,
    thy_asserts = fms ++ thy_asserts
  }
 where
  (abs,fms) = unzip (map axiomatize thy_funcs)

axiomatize :: forall a . Function a -> (Signature a, Formula a)
axiomatize fn@Function{..} =
  ( Signature func_name (funcType fn)
  , Formula Assert func_tvs
     (mkQuant Forall func_args (lhs === func_body))
  )
 where
  lhs = applyFunction fn (map TyVar func_tvs) (map Lcl func_args)

-- | Makes function definitions into case by converting case to
--   left hand side pattern matching.
axiomatizeFuncdefs2 :: Name a => (Expr a -> Maybe (Expr a)) -> Theory a -> Theory a
axiomatizeFuncdefs2 min_pred thy@Theory{..} =
  thy{
    thy_funcs   = [],
    thy_sigs    = thy_sigs ++ abs,
    thy_asserts = concat fms ++ thy_asserts
  }
 where
  scp = scope thy
  (abs,fms) = unzip (map (axiomatize2 min_pred scp) thy_funcs)

axiomatize2 :: forall a . Ord a => (Expr a -> Maybe (Expr a)) -> Scope a -> Function a -> (Signature a, [Formula a])
axiomatize2 min_pred scp fn@Function{..} =
  ( Signature func_name (funcType fn)
  , map (Formula Assert func_tvs)
     (ax func_args
         (maybeToList (min_pred (func_app (map Lcl func_args))))
         (map Lcl func_args)
         func_body)
  )
  where
  func_app = applyFunction fn (map TyVar func_tvs)

  -- ax vars pre args body
  --   ~=
  -- forall vars . pre => f(args) = body
  ax :: [Local a] -> [Expr a] -> [Expr a] -> Expr a -> [Expr a]
  ax vars pre args e0 = case e0 of
    Match s (Case Default def_rhs:alts) ->
         ax vars (pre ++ map (invert_pat s . case_pat) alts) args def_rhs
      ++ ax_alts s alts
    Match s alts -> ax_alts s alts
    Let x b e    -> ax (vars ++ [x]) (pre ++ [Lcl x === b]) args e
    Lam{}        -> __
    Quant{}      -> __
    _            ->
      -- e0 should now only be (:@:) and Lcl
      [mkQuant Forall vars (pre ===> func_app args === e0)]
    where
    invert_pat :: Expr a -> Pattern a -> Expr a
    invert_pat _ Default      = __
    invert_pat s (LitPat lit) = s =/= literal lit
    invert_pat s (ConPat k _) = s =/= (Gbl k :@: [ Gbl (projector dt c i (gbl_args k)) :@: [s] | i <- [0..length cargs-1] ])
      where
      Just (dt,c@(Constructor _ _ cargs)) = lookupConstructor (gbl_name k) scp

    ax_alts :: Expr a -> [Case a] -> [Expr a]
    ax_alts s alts = concat [ ax_pat s pat rhs | Case pat rhs <- alts ]
      where
      ax_pat :: Expr a -> Pattern a -> Expr a -> [Expr a]
      ax_pat _ Default       _   = __
      ax_pat s (LitPat lit)  rhs = rec [] rhs s (literal lit)
      ax_pat s (ConPat k bs) rhs = rec bs rhs s (Gbl k :@: map Lcl bs)

      rec :: [Local a] -> Expr a -> Expr a -> Expr a -> [Expr a]
      rec new e scrut pat_expr =
           maybeToList
             (fmap (\ min_scrut -> mkQuant Forall vars (pre ===> min_scrut))
                   (min_pred scrut))
        ++ case scrut of
             Lcl x ->
               let su = unsafeSubst pat_expr x
               in  ax (delete x vars ++ new) (map su pre) (map su args) (su e)
             _ ->  ax (vars ++ new) (pre ++ [scrut === pat_expr]) args e

