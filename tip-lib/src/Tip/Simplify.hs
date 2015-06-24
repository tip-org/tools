{-# LANGUAGE FlexibleContexts, RecordWildCards, ScopedTypeVariables, ViewPatterns, PatternGuards #-}
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
    remove_variable_scrutinee_in_branches :: Bool,
    -- ^ transform
    -- @(match x (case (K y) (e x y)))@
    -- to
    -- @(match x (case (K y) (e (K y) y))@
    -- This is useful for triggering other known-case simplifications,
    -- and is therefore on by default.
    should_inline :: Occurrences -> Maybe (Scope a) -> Expr a -> Bool,
    -- ^ Inlining predicate
    inline_match  :: Bool
    -- ^ Allow function inlining to introduce match
  }

newtype Occurrences = Occurrences Int

-- | Gentle, but without inlining
gentlyNoInline :: SimplifyOpts a
gentlyNoInline = gently { should_inline = \ _ _ _ -> False }

-- | Gentle options: if there is risk for code duplication, only inline atomic expressions
gently :: SimplifyOpts a
gently       = SimplifyOpts True True (\ (Occurrences occ) _ e -> occ <= 1 || atomic e) True

-- | Aggressive options: inline everything that might plausibly lead to simplification
aggressively :: Name a => SimplifyOpts a
aggressively = SimplifyOpts True True (\ (Occurrences occ) mscp e -> occ <= 1 || useful mscp e) True
  where
    useful _ Lam{} = True
    useful mscp (f :@: _) = isConstructor mscp f
    useful _ _ = False

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
      let
        share e1 | e1 /= e0  = return e1
                 | otherwise = return e0 in
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

        Match _ [Case Default body] -> hooray $ return body

        Match e (Case Default def:cases)
          | TyCon ty args <- exprType e,
            Just (d, c@Constructor{..}) <- missingCase mscp ty cases -> do
              lcls <- lift (mapM (refreshLocal . uncurry Local) con_args)
              let pat = ConPat (constructor d c args) lcls
              aux (Match e (Case pat def:cases))

        Match e [Case _ e1,Case (LitPat (Bool b)) e2]
          | e1 == bool (not b) && e2 == bool b -> hooray $ return e
          | e1 == bool b && e2 == bool (not b) -> hooray $ return (neg e)

        Match (Let x e body) alts | touch_lets ->
          aux (Let x e (Match body alts))

        Match (hd :@: args) alts | isConstructor mscp hd ->
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

        Match (Lcl x) alts | remove_variable_scrutinee_in_branches ->
          Match (Lcl x) <$> sequence
          [ Case pat <$> case pat of
              ConPat g bs -> subst ((Gbl g :@: map Lcl bs) /// x) rhs
              LitPat l    -> subst (literal l /// x) rhs
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

        Builtin Equal :@: [litView -> Just s,litView -> Just t] -> hooray $ return (bool (s == t))

        Builtin Distinct :@: [litView -> Just s,litView -> Just t] -> hooray $ return (bool (s /= t))

        Builtin Not     :@: [e]      -> share (neg e)
        Builtin And     :@: [e1, e2] | e1 == e2  -> return e1
                                     | otherwise -> share (e1 /\ e2)
        Builtin Or      :@: [e1, e2] | e1 == e2  -> return e1
                                     | otherwise -> share (e1 \/ e2)
        Builtin Implies :@: [e1, e2] -> share (e1 ==> e2)

        Builtin Equal :@: [e1, e2] ->
          case exprType e1 of
            t@(_ :=>: _) -> hooray $ go t e1 e2 []
              where
              go (args :=>: rest) u v lcls =
                do more <- lift (mapM freshLocal args)
                   go rest (apply u (map Lcl more))
                           (apply v (map Lcl more))
                           (lcls ++ more)
              go _ u v lcls = return (mkQuant Forall lcls (u === v))
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
                  if (simplified && (inline_match || not (containsMatch e2))) || atomic func_body
                  then hooray $ return e2
                  else return (Gbl gbl :@: ts)
            _ -> return (Gbl gbl :@: ts)

        _ -> return e0

    inlineable body var val = should_inline (Occurrences (occurrences var body)) mscp val
    mscp = fmap scope mthy

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
      if e == Lcl old then hooray $ lift (freshen new) else return e

    hooray x = do
      tell (Any True)
      x

    boo x = censor (const (Any False)) x

isConstructor :: Name a => Maybe (Scope a) -> Head a -> Bool
isConstructor _ (Builtin Lit{}) = True
isConstructor mscp (Gbl gbl) = isJust $ do
  scp <- mscp
  lookupConstructor (gbl_name gbl) scp
isConstructor _ _ = False

missingCase :: Name a => Maybe (Scope a) -> a -> [Case a] -> Maybe (Datatype a, Constructor a)
missingCase mscp tc cases = do
  scp <- mscp
  dt@Datatype{..} <- lookupDatatype tc scp
  let matched Constructor{..} =
        con_name `elem` [ gbl_name pat_con | ConPat{..} <- map case_pat cases ]
  case filter (not . matched) data_cons of
    [con] -> return (dt, con)
    _     -> Nothing
