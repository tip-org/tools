{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.AxiomatizeFuncdefs where

#include "errors.h"
import Tip
import Tip.Fresh

import Data.Generics.Geniplate
import Control.Applicative

--conProjs :: Project a => Global a -> [Global a]
conProjs = undefined
{- (Global k (PolyType tvs arg_tys res_ty) ts _)
  = [ Global (project k i) (PolyType tvs [res_ty] arg_ty) ts ProjectNS
    | (i,arg_ty) <- zip [0..] arg_tys
    ]
    -}

axiomatizeFuncdefs :: Theory a -> Theory a
axiomatizeFuncdefs thy@Theory{..} =
  thy{
    thy_funcs   = [],
    thy_sigs    = thy_sigs ++ abs,
    thy_asserts = fms ++ thy_asserts
  }
 where
  (abs,fms) = unzip (map axiomatize thy_funcs)

-- Passes needed afterwards:
--
-- 1)  x = e ==> F[x] ~~> F[e]
--
-- 2)
--     all x (D => (all y . E) /\ (all z . F))
-- ~~>
--     all x ((D => all y . E) /\ (D => all z . F))
-- ~~>
--     (all x y (D => E)) /\ (all x z (D => F))
--
-- (TODO)

axiomatize :: forall a . Function a -> (Signature a, Formula a)
axiomatize fn@Function{..} =
  ( Signature func_name (funcType fn)
  , Formula Assert func_tvs (ax func_body)
  )
 where
  lhs = applyFunction fn (map TyVar func_tvs) (map Lcl func_args)

  ax :: Expr a -> Expr a
  ax e0 = case e0 of
    Match s (Case Default def_rhs:alts) -> invert_alts s alts def_rhs /\ ax_alts s alts
    Match s alts -> ax_alts s alts
    Let{}        -> __ -- could use ==> while Let is neither recursive nor polymorphic
    Lam{}        -> __
    Quant{}      -> __
    _            -> lhs === e0 -- e0 should now only be (:@:) and Lcl
   where
    invert_alts :: Expr a -> [Case a] -> Expr a -> Expr a
    invert_alts _ []                def_rhs = def_rhs
    invert_alts s (Case pat _:alts) def_rhs = s === invert_pat s pat \/
                                              invert_alts s alts def_rhs
     where
      invert_pat :: Expr a -> Pattern a -> Expr a
      invert_pat _ Default      = __
      invert_pat _ (LitPat lit) = literal lit
      invert_pat s (ConPat k _) = Gbl k :@: [ Gbl p :@: [s] | p <- conProjs k ]

    ax_alts :: Expr a -> [Case a] -> Expr a
    ax_alts s alts = ands [ ax_pat s pat rhs | Case pat rhs <- alts ]
     where
      ax_pat :: Expr a -> Pattern a -> Expr a -> Expr a
      ax_pat _ Default       _   = __
      ax_pat s (LitPat lit)  rhs = s === literal lit ==> ax rhs
      ax_pat s (ConPat k bs) rhs = mkQuant Forall bs
                                     (s === Gbl k :@: map Lcl bs ==> ax rhs)

