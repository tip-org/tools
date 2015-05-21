{-# LANGUAGE FlexibleContexts, RecordWildCards, ScopedTypeVariables #-}
module Tip.Simplify where

import Tip.Core
import Tip.Scope
import Tip.Fresh
import Data.Generics.Geniplate
import Data.List
import Data.Maybe
import Control.Applicative

-- | Options for the simplifier
data SimplifyOpts a =
  SimplifyOpts {
    touch_lets    :: Bool,
    -- ^ Allow simplifications on lets
    should_inline :: Expr a -> Bool
    -- ^ Inlining predicate
  }

-- | Gentle options: if there is risk for code duplication, only inline atomic expressions
gently :: SimplifyOpts a
gently       = SimplifyOpts True atomic

-- | Aggressive options: inline everything
aggressively :: SimplifyOpts a
aggressively = SimplifyOpts True (const True)

-- | Simplify an entire theory
simplifyTheory :: Name a => SimplifyOpts a -> Theory a -> Fresh (Theory a)
simplifyTheory opts thy = simplifyExprIn (Just thy) opts thy

-- | Simplify an expression, without knowing its theory
simplifyExpr :: forall f a. (TransformBiM Fresh (Expr a) (f a), Name a) => SimplifyOpts a -> f a -> Fresh (f a)
simplifyExpr opts = simplifyExprIn Nothing opts

-- | Simplify an expression within a theory
simplifyExprIn :: forall f a. (TransformBiM Fresh (Expr a) (f a), Name a) => Maybe (Theory a) -> SimplifyOpts a -> f a -> Fresh (f a)
simplifyExprIn mthy opts@SimplifyOpts{..} = aux
  where
    aux :: forall f. TransformBiM Fresh (Expr a) (f a) => f a -> Fresh (f a)
    aux = transformExprInM $ \e0 ->
      case e0 of
        Builtin At :@: (Lam vars body:args) -> do
          let (remove, keep) = partition (uncurry (inlineable body)) (zip vars args)
          body' <- substMany remove body
          let e' = case keep of
                     [] -> body'
                     _  -> apply (Lam (map fst keep) body') (map snd keep)
          aux e'

        Let var val body | touch_lets && inlineable body var val ->
          (val // var) body >>= aux

        Match e [Case _ e1,Case (LitPat (Bool b)) e2]
          | e1 == bool (not b) && e2 == bool b -> return e
          | e1 == bool b && e2 == bool (not b) -> return (neg e)

        Match (Let var val body) alts | touch_lets ->
          aux (Let var val (Match body alts))

        Match (Lcl x) alts -> Match (Lcl x) <$> sequence
          [ Case pat <$> case pat of
              ConPat g bs -> substMatched x (Gbl g :@: map Lcl bs) rhs
              -- LitPat l    -> substMatched x (literal l) rhs
              _           -> return rhs
          | Case pat rhs <- alts
          ]

        Match _ [Case Default body] -> return body

        Match (hd :@: args) alts | isConstructor hd ->
          -- We use reverse because the default case comes first and we want it last
          case filter (matches hd . case_pat) (reverse alts) of
            [] -> return e0
            Case (ConPat _ lcls) body:_ ->
              aux $
                foldr (uncurry Let) body (zip lcls args)
            Case _ body:_ -> return body
          where
            matches (Gbl gbl) (ConPat gbl' _) = gbl == gbl'
            matches (Builtin (Lit lit)) (LitPat lit') = lit == lit'
            matches _ Default = True
            matches _ _ = False

        Builtin Equal :@: [Builtin (Lit (Bool x)) :@: [], t]
          | x -> return t
          | otherwise -> return $ neg t

        Builtin Equal :@: [t, Builtin (Lit (Bool x)) :@: []]
          | x -> return t
          | otherwise -> return $ neg t

        Builtin Equal :@: [t, u] ->
          case exprType t of
            args :=>: _ -> do
              lcls <- mapM freshLocal args
              aux $
                mkQuant Forall lcls (apply t (map Lcl lcls) === apply u (map Lcl lcls))
            _ -> return e0

        _ -> return e0

    substMatched x k_xs = transformExprInM $ \ e0 ->
      case e0 of
        Match (Lcl y) alts | x == y -> aux (Match k_xs alts)
        _ | e0 == k_xs -> return (Lcl x)
        _ -> return e0

    inlineable body var val = should_inline val || occurrences var body <= 1
    occurrences var body = length (filter (== var) (universeBi body))
    mscp = fmap scope mthy
    isConstructor (Builtin Lit{}) = True
    isConstructor (Gbl gbl) = isJust $ do
      scp <- mscp
      lookupConstructor (gbl_name gbl) scp
    isConstructor _ = False


