{-# LANGUAGE FlexibleContexts, RecordWildCards #-}
module Tip.Simplify where

import Tip
import Tip.Fresh
import Data.Generics.Geniplate
import Data.List

data SimplifyOpts a =
  SimplifyOpts {
    should_inline :: Expr a -> Bool
  }

gently, aggressively :: SimplifyOpts a
gently       = SimplifyOpts atomic
aggressively = SimplifyOpts (const True)

simplifyExpr :: (TransformBiM Fresh (Expr a) (f a), Name a) => SimplifyOpts a -> f a -> Fresh (f a)
simplifyExpr opts@SimplifyOpts{..} = transformExprInM $ \e ->
  case e of
    Builtin (At _) :@: (Lam vars body:args) -> do
      let (remove, keep) = partition (uncurry (inlineable body)) (zip vars args)
      body' <- substMany remove body
      let e' = case keep of
                 [] -> body
                 _  -> apply (Lam (map fst keep) body') (map snd keep)
      simplifyExpr opts e'

    Let var val body | inlineable body var val ->
      (val // var) body >>= simplifyExpr opts

    Match (Let var val body) alts ->
      simplifyExpr opts (Let var val (Match body alts))

    Match (hd :@: args) alts ->
      -- We use reverse because the default case comes first and we want it last
      case filter (matches hd . case_pat) (reverse alts) of
        [] -> return e
        Case Default body:_ -> return body
        Case (ConPat _ lcls) body:_ ->
          simplifyExpr opts $
            foldr (uncurry Let) body (zip lcls args)
        Case (LitPat _) body:_ -> return body
      where
        matches (Gbl gbl) (ConPat gbl' _) = gbl == gbl'
        matches (Builtin (Lit lit)) (LitPat lit') = lit == lit'
        matches _ Default = True
        matches _ _ = False

    _ -> return e
  where
    inlineable body var val = should_inline val || occurrences var body <= 1
    occurrences var body = length (filter (== var) (universeBi body))
