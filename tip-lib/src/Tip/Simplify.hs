{-# LANGUAGE FlexibleContexts, RecordWildCards #-}
module Tip.Simplify where

import Tip
import Tip.Fresh
import Data.Generics.Geniplate
import Data.List
import Control.Applicative

data SimplifyOpts a =
  SimplifyOpts {
    touch_lets    :: Bool,
    should_inline :: Expr a -> Bool
  }

gently, aggressively :: SimplifyOpts a
gently       = SimplifyOpts True atomic
aggressively = SimplifyOpts True (const True)

simplifyExpr :: (TransformBiM Fresh (Expr a) (f a), Name a) => SimplifyOpts a -> f a -> Fresh (f a)
simplifyExpr opts@SimplifyOpts{..} = transformExprInM $ \e0 ->
  case e0 of
    Builtin At :@: (Lam vars body:args) -> do
      let (remove, keep) = partition (uncurry (inlineable body)) (zip vars args)
      body' <- substMany remove body
      let e' = case keep of
                 [] -> body'
                 _  -> apply (Lam (map fst keep) body') (map snd keep)
      simplifyExpr opts e'

    Let var val body | touch_lets && inlineable body var val ->
      (val // var) body >>= simplifyExpr opts

    Match e [Case _ e1,Case (LitPat (Bool b)) e2]
      | e1 == bool (not b) && e2 == bool b -> return e
      | e1 == bool b && e2 == bool (not b) -> return (neg e)

    Match (Let var val body) alts | touch_lets ->
      simplifyExpr opts (Let var val (Match body alts))

    Match (Lcl x) alts -> Match (Lcl x) <$> sequence
      [ Case pat <$> case pat of
          ConPat g bs -> substMatched opts x (Gbl g :@: map Lcl bs) rhs
          -- LitPat l    -> substMatched opts x (literal l) rhs
          _           -> return rhs
      | Case pat rhs <- alts
      ]

    Match _ [Case Default body] -> return body

    Match (hd :@: args) alts ->
      -- We use reverse because the default case comes first and we want it last
      case filter (matches hd . case_pat) (reverse alts) of
        [] -> return e0
        Case (ConPat _ lcls) body:_ ->
          simplifyExpr opts $
            foldr (uncurry Let) body (zip lcls args)
        Case (LitPat _) body:_ -> return body
      where
        matches (Gbl gbl) (ConPat gbl' _) = gbl == gbl'
        matches (Builtin (Lit lit)) (LitPat lit') = lit == lit'
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
          simplifyExpr opts $
            mkQuant Forall lcls (apply t (map Lcl lcls) === apply u (map Lcl lcls))
        _ -> return e0

    _ -> return e0
  where
    inlineable body var val = should_inline val || occurrences var body <= 1
    occurrences var body = length (filter (== var) (universeBi body))

substMatched :: (Name a) => SimplifyOpts a -> Local a -> Expr a -> Expr a -> Fresh (Expr a)
substMatched opts x k_xs = transformExprInM $ \ e0 ->
  case e0 of
    Match (Lcl y) alts | x == y -> simplifyExpr opts (Match k_xs alts)
    _ | e0 == k_xs -> return (Lcl x)
    _ -> return e0

