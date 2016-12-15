{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tip.Pass.AxiomatizeFuncdefs where

#include "errors.h"
import Tip.Core
import Tip.Fresh
import Tip.Scope

import Data.List (delete, nub, (\\))
import Data.Generics.Geniplate
import Control.Applicative

import Tip.Pass.Conjecture

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
  ( Signature func_name func_attrs (funcType fn)
  , putAttr definition () $
    Formula Assert func_attrs func_tvs
     (mkQuant Forall func_args (lhs === func_body))
  )
 where
  lhs = applyFunction fn (map TyVar func_tvs) (map Lcl func_args)

-- | Makes function definitions into case by converting case to
--   left hand side pattern matching.
axiomatizeFuncdefs2 :: Name a => Theory a -> Theory a
axiomatizeFuncdefs2 thy@Theory{..} =
  thy{
    thy_funcs   = [],
    thy_sigs    = thy_sigs ++ abs,
    thy_asserts = concat fms ++ thy_asserts
  }
 where
  scp = scope thy
  (abs,fms) = unzip (map (axiomatize2 scp) thy_funcs)

axiomatize2 :: forall a . Ord a => Scope a -> Function a -> (Signature a, [Formula a])
axiomatize2 scp fn@Function{..} =
  ( Signature func_name func_attrs (funcType fn)
  , [ putAttr definition () $
      Formula Assert func_attrs func_tvs $
        mkQuant Forall vars
          (pre ===> applyFunction fn (map TyVar func_tvs) args === body)
    | (vars, pre, args, body) <- functionContexts scp fn
    ]
  )

recursionInduction :: forall a . Name a => Int -> [Int] -> Theory a -> Fresh [Theory a]
recursionInduction f_num xs_nums thy =
  case theoryGoals thy of
    ([],_) -> return [thy]
    (Formula Prove attrs tvs body:gs,assums) ->
      do let (vars,e) = forallView body
         let f = nub [ g | g@Global{..} <- universeBi e ] !! f_num
         let fn:_ = [ h | h@Function{..} <- thy_funcs thy
                        , func_name == gbl_name f ]
         let ctxts = functionContexts (scope thy) fn
         let xs = map (vars !!) xs_nums
         let vars' = vars \\ xs
         fms <-
           sequence
             [ do ihs <-
                    sequence
                      [ do vars'' <- mapM refreshLocal vars'
                           mkQuant Forall vars'' <$>
                             substMany (zip vars' (map Lcl vars'') ++ zip xs f_args) e
                      | Gbl (Global f' _ _) :@: f_args <- universeBi body
                      , f' == gbl_name f
                      ]
                  e' <- substMany (zip xs p_args) e
                  return $
                    mkQuant Forall (vars' ++ qs) ((pre ++ ihs) ===> e')
             | (qs, pre, p_args, body) <- ctxts
             ]
         return
           [ thy { thy_asserts = Formula Prove attrs tvs fm:gs ++ assums }
           | fm <- fms
           ]

type Contexts a = [([Local a], [Expr a], [Expr a], Expr a)]

-- functionContexts vars pre args body
--   ~=
--    [(vars, pre, args, body)]
-- where each is
--    forall vars . pre => f(args) = body
-- or for rec ind
--    forall vars . pre & P( ... body ...) => P(args)
functionContexts :: forall a . Ord a => Scope a -> Function a -> Contexts a
functionContexts scp Function{..} = go func_args [] (map Lcl func_args) func_body
  where
  go :: [Local a] -> [Expr a] -> [Expr a] -> Expr a -> Contexts a
  go vars pre args e0 = case e0 of
    Match s (Case Default def_rhs:alts) -> go vars (pre ++ map (invert_pat s . case_pat) alts) args def_rhs ++ go_alts s alts
    Match s alts -> go_alts s alts
    Let x b e    -> go (vars ++ [x]) (pre ++ [Lcl x === b]) args e
    Lam{}        -> __
    Quant{}      -> __
    _            -> [(vars, pre, args, e0)]
    where
    invert_pat :: Expr a -> Pattern a -> Expr a
    invert_pat _ Default      = __
    invert_pat s (LitPat lit) = s =/= literal lit
    invert_pat s (ConPat k _) = s =/= (Gbl k :@: [ Gbl (projector dt c i (gbl_args k)) :@: [s] | i <- [0..length cargs-1] ])
      where
      Just (dt,c@(Constructor{con_args = cargs})) = lookupConstructor (gbl_name k) scp

    go_alts :: Expr a -> [Case a] -> Contexts a
    go_alts s alts = concat [ go_pat s pat rhs | Case pat rhs <- alts ]
      where
      go_pat :: Expr a -> Pattern a -> Expr a -> Contexts a
      go_pat _ Default       _   = __
      go_pat s (LitPat lit)  rhs = rec [] rhs s (literal lit)
      go_pat s (ConPat k bs) rhs = rec bs rhs s (Gbl k :@: map Lcl bs)

      rec :: [Local a] -> Expr a -> Expr a -> Expr a -> Contexts a
      rec new e (Lcl x) pat_expr =
        let su = unsafeSubst pat_expr x
        in  go (delete x vars ++ new) (map su pre) (map su args) (su e)

      rec new e scrut   pat_expr = go (vars ++ new) (pre ++ [scrut === pat_expr]) args e

