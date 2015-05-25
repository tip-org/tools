{-# LANGUAGE FlexibleContexts, RecordWildCards, ScopedTypeVariables #-}
module Tip.Simplify where

import Tip.Core
import Tip.Scope
import Tip.Fresh
import Data.Generics.Geniplate
import Data.List
import Data.Maybe
import Data.Monoid
import Control.Applicative
import Control.Monad
import qualified Data.Map as Map
import Tip.Writer

-- | Options for the simplifier
data SimplifyOpts a =
  SimplifyOpts {
    touch_lets    :: Bool,
    -- ^ Allow simplifications on lets
    should_inline :: Expr a -> Bool,
    -- ^ Inlining predicate
    inline_match  :: Bool
    -- ^ Allow function inlining to introduce match
  }

-- | Gentle options: if there is risk for code duplication, only inline atomic expressions
gently :: SimplifyOpts a
gently       = SimplifyOpts True atomic True

-- | Aggressive options: inline everything
aggressively :: SimplifyOpts a
aggressively = SimplifyOpts True (const True) True

-- | Simplify an entire theory
simplifyTheory :: Name a => SimplifyOpts a -> Theory a -> Fresh (Theory a)
simplifyTheory opts thy@Theory{..} = do
  thy_funcs   <- mapM (simplifyExprIn (Just thy) opts) thy_funcs
  thy_asserts <- mapM (simplifyExprIn (Just thy) opts{inline_match = False}) thy_asserts
  return Theory{..}

-- | Simplify an expression, without knowing its theory
simplifyExpr :: forall f a. (TransformBiM (WriterT Any Fresh) (Expr a) (f a), Name a) => SimplifyOpts a -> f a -> Fresh (f a)
simplifyExpr opts = simplifyExprIn Nothing opts

-- | Simplify an expression within a theory
simplifyExprIn :: forall f a. (TransformBiM (WriterT Any Fresh) (Expr a) (f a), Name a) => Maybe (Theory a) -> SimplifyOpts a -> f a -> Fresh (f a)
simplifyExprIn mthy opts@SimplifyOpts{..} = fmap fst . runWriterT . aux
  where
    {-# SPECIALISE aux :: Expr a -> WriterT Any Fresh (Expr a) #-}
    aux :: forall f. TransformBiM (WriterT Any Fresh) (Expr a) (f a) => f a -> WriterT Any Fresh (f a)
    aux = transformBiM $ \e0 ->
      case e0 of
        Builtin At :@: (Lam vars body:args) ->
          hooray $
          aux (foldr (uncurry Let) body (zip vars args))

        Let x e body | touch_lets && (atomic e || occurrences x body <= 1) ->
          lift ((e // x) body) >>= aux

        Let x e body | touch_lets && inlineable body x e ->
          do e1 <- lift ((e // x) body)
             (e2, Any simplified) <- lift (runWriterT (aux e1))
             if simplified then hooray $ return e2 else return e0

        Match e [Case _ e1,Case (LitPat (Bool b)) e2]
          | e1 == bool (not b) && e2 == bool b -> hooray $ return e
          | e1 == bool b && e2 == bool (not b) -> hooray $ return (neg e)

        Match (Let x e body) alts | touch_lets ->
          aux (Let x e (Match body alts))

        Match _ [Case Default body] -> hooray $ return body

        Match (hd :@: args) alts | isConstructor hd ->
          -- We use reverse because the default case comes first and we want it last
          case filter (matches hd . case_pat) (reverse alts) of
            [] -> return e0
            Case (ConPat _ lcls) body:_ ->
              hooray $
              aux $
                foldr (uncurry Let) body (zip lcls args)
            Case _ body:_ -> hooray $ return body
          where
            matches (Gbl gbl) (ConPat gbl' _) = gbl == gbl'
            matches (Builtin (Lit lit)) (LitPat lit') = lit == lit'
            matches _ Default = True
            matches _ _ = False

        Match e alts ->
          Match e <$> sequence
          [ Case pat <$> case pat of
              ConPat g bs -> subst ((Gbl g :@: map Lcl bs) /// e) rhs
              LitPat l    -> subst (literal l /// e) rhs
              _           -> return rhs
          | Case pat rhs <- alts
          ]
          where
            subst f e = do
              (e', Any successful) <- lift (runWriterT (f e))
              if successful then aux e' else return e

        Builtin Equal :@: [Builtin (Lit (Bool x)) :@: [], t]
          | x -> hooray $ return t
          | otherwise -> hooray $ return $ neg t

        Builtin Equal :@: [t, Builtin (Lit (Bool x)) :@: []]
          | x -> hooray $ return t
          | otherwise -> hooray $ return $ neg t

        Builtin Equal :@: [t, u] ->
          case exprType t of
            args :=>: _ -> hooray $ do
              lcls <- lift (mapM freshLocal args)
              aux $
                mkQuant Forall lcls (apply t (map Lcl lcls) === apply u (map Lcl lcls))
            _ -> return e0

        Gbl gbl@Global{..} :@: ts ->
          case Map.lookup gbl_name inlinings of
            Just func@Function{..}
              | and [ inlineable func_body x t | (x, t) <- zip func_args ts ] -> do
                  func_body <- boo $ aux func_body
                  e1 <-
                    transformTypeInExpr (applyType func_tvs gbl_args) <$>
                      lift (substMany (zip func_args ts) func_body)
                  (e2, Any simplified) <- lift (runWriterT (aux e1))
                  if simplified && (inline_match || not (containsMatch e2))
                  then hooray $ return e2
                  else return (Gbl gbl :@: ts)
            _ -> return (Gbl gbl :@: ts)

        _ -> return e0

    inlineable body var val = should_inline val || occurrences var body <= 1
    mscp = fmap scope mthy
    isConstructor (Builtin Lit{}) = True
    isConstructor (Gbl gbl) = isJust $ do
      scp <- mscp
      lookupConstructor (gbl_name gbl) scp
    isConstructor _ = False

    isRecursiveGroup [fun] = defines fun `elem` uses fun
    isRecursiveGroup _     = True

    inlinings =
      case mthy of
        Nothing -> Map.empty
        Just Theory{..} ->
          Map.fromList . map (\fun -> (func_name fun, fun)) .
          concat . filter (not . isRecursiveGroup) . topsort $ thy_funcs

    containsMatch e = not (null [ e' | e'@Match{} <- universe e ])

    new /// old = transformExprM $ \e ->
      if e == old then hooray $ lift (freshen new) else return e

    hooray x = do
      tell (Any True)
      x

    boo x = censor (const (Any False)) x
