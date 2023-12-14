{-# LANGUAGE FlexibleContexts, RecordWildCards, ScopedTypeVariables, ViewPatterns, PatternGuards #-}
module Tip.Simplify where

import Tip.Core
import Tip.Scope
import Tip.Fresh
import Data.Generics.Geniplate
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Foldable as F
import qualified Data.Map as Map
import Tip.Writer
import Tip.Utils

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
        gbl :@: args
          | touch_lets,
            ((i, Let x e body):_) <- [(i, e) | (i, e@Let{}) <- zip [0..] args] -> do
          y <- lift (refreshLocal x)
          body' <- lift ((Lcl y // x) body)
          let e0' = Let y e (gbl :@: (take i args ++ [body'] ++ drop (i+1) args))
          hooray $ aux e0'

        Builtin At :@: (Lam vars body:args) ->
          hooray $
          aux (foldr (uncurry Let) body (zip vars args))

        Let x e body | touch_lets && (atomic e || occurrences x body <= 1) ->
          lift ((e // x) body) >>= aux

        Let x e body | touch_lets && inlineable body x e ->
          do e1 <- lift ((e // x) body)
             (e2, Any simplified) <- lift (runWriterT (aux e1))
             if simplified then hooray $ return e2 else return e0

        Quant NoInfo q xs (Quant NoInfo q' ys form) | q == q' ->
          hooray $
          return (Quant NoInfo q (xs ++ ys) form)

        Match _ [Case Default body] -> hooray $ return body

        -- eta for match
        Match e brs
          | and [ case br of
                    Case (ConPat g as) (Gbl k :@: es) ->
                      g == k && and [ Lcl a == e | (a,e) <- zip as es ]
                    Case _ e' -> e == e'
                | br <- brs
                ]
          -> hooray $ return e

        -- let x = case e of pi -> ai
        -- in  case e of
        --       pi -> bi
        --
        -- => case e of pi -> let xi = ai in bi[xi/x]
        Let x (Match e as) rest
          | (Match e' bs,ctx):_ <-
              [ (Match e' bs,ctx)
              | (Match e' bs,ctx) <- usePoints (lcl_name x) rest
              , e == e'
              ]
          -> do brs <-
                  sequence
                    [ do xi <- lift (refreshLocal x)
                         return (Case p (Let xi a (unsafeSubst (Lcl xi) x b)))
                    | (p,a,b) <- align as bs
                    ]
                return (ctx (Match e brs))

        Match e (Case Default (Match e' cases'):cases) | e == e' ->
          hooray $ aux $
          caseExpr e (cases ++ filter (not . dead . case_pat) cases')
          where
            dead (LitPat l)   = LitPat l `elem` map case_pat cases
            dead (ConPat{..}) =
              gbl_name pat_con `elem`
                [ gbl_name pat_con | ConPat{..} <- map case_pat cases ]
            dead Default = False

        Match e (Case Default def:cases)
          | TyCon ty args <- exprType e,
            Just (d, c@Constructor{..}) <- missingCase mscp ty cases -> do
              let gbl = constructor d c args
              pat <- lift (fmap (ConPat gbl) (freshArgs gbl))
              aux (caseExpr e (cases ++ [Case pat def]))

        Match e [Case _ e1,Case (LitPat (Bool b)) e2]
          | e1 == bool (not b) && e2 == bool b -> hooray $ return e
          | e1 == bool b && e2 == bool (not b) -> hooray $ return (neg e)

        Match (Let x e body) alts | touch_lets ->
          aux (Let x e (Match body alts))

        Match e alts
          | Just e' <- tryMatch mscp e alts -> hooray $ aux e'

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

        -- cons(x,y) == nil ~> false
        -- cons(x,y) /= nil ~> true
        --
        -- cons(x1,y1) == cons(x2,y2) ~> x1==x2 & y1==y2
        -- cons(x1,y1) /= cons(x2,y2) ~> x1/=x2 | y1/=y2
        Builtin eq_op :@: [Gbl k :@: kargs,Gbl j :@: jargs]
          | Just scp <- mscp
          , Just (_,Constructor{con_name = kk}) <- lookupConstructor (gbl_name k) scp
          , Just (_,Constructor{con_name = jj}) <- lookupConstructor (gbl_name j) scp
          , Just res <- case (eq_op, kk == jj) of
                          (Equal   ,False) -> Just falseExpr
                          (Distinct,False) -> Just trueExpr
                          (Equal,   True)  -> Just (ands (zipWith (===) kargs jargs))
                          (Distinct,True)  -> Just (ors  (zipWith (=/=) kargs jargs))
                          _                -> Nothing
          -> hooray $ aux res

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
        Builtin NumGe :@: [e1, e2] -> hooray $ return (Builtin NumLe :@: [e2,e1])
        Builtin NumGt :@: [e1,e2]  -> hooray $ return (Builtin NumLt :@: [e2,e1])
        -- Projection applied to a constructor
        -- e.g. (head (Cons x xs)) -> x
        Gbl Global{gbl_name = proj_name} :@: [Gbl Global{gbl_name = con_name} :@: args]
          | Just scp <- mscp,
            Just (_, con) <- lookupConstructor con_name scp,
            Just n <- elemIndex proj_name (map fst (con_args con)) ->
            hooray $ return $ args !! n

        -- Discriminator applied to a constructor
        -- e.g. (is-Cons (Cons x xs)) -> true
        Gbl Global{gbl_name = discrim_name} :@: [Gbl Global{gbl_name = con_name} :@: args]
          | Just scp <- mscp,
            Just (dt, con) <- lookupConstructor con_name scp,
            discrim_name `elem` map con_discrim (data_cons dt) ->
            hooray $ return $ bool $ con_discrim con == discrim_name

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

tryMatch :: Name a => Maybe (Scope a) -> Expr a -> [Case a] -> Maybe (Expr a)
tryMatch mscp (hd :@: args) alts | isConstructor mscp hd =
  -- We use reverse because the default case comes first and we want it last
  case filter (matches hd . case_pat) (reverse alts) of
    [] -> Nothing
    Case (ConPat _ lcls) body:_ ->
      Just $ foldr (uncurry Let) body (zip lcls args)
    Case _ body:_ -> Just body
  where
    matches (Gbl gbl) (ConPat gbl' _) = gbl == gbl'
    matches (Builtin (Lit lit)) (LitPat lit') = lit == lit'
    matches _ Default = True
    matches _ _ = False
tryMatch _ _ _ = Nothing

align :: Ord a => [Case a] -> [Case a] -> [(Pattern a,Expr a,Expr a)]
align ls rs =
  [ (Default,l,r)
  | (Just l,Just r) <- [(mdl,mdr)]
  ] ++
  [ case (find (lk p . case_pat) ls,find (lk p . case_pat) rs) of
      (Just (Case pl el), Just (Case pr er)) -> (pr,su pl pr el,er)
      (Just (Case p e),   Nothing)           -> (p,e,dr)
      (Nothing,           Just (Case p e))   -> (p,dl,e)
      (Nothing,           Nothing)           -> error "not sure why this case should be impossible"
  | p <- pats
  ]
  where
  pats = usort (mapMaybe (tr . case_pat) (ls ++ rs))

  mdl@(~(Just dl)) = case ls of Case Default e:_ -> Just e
                                _                -> Nothing
  mdr@(~(Just dr)) = case ls of Case Default e:_ -> Just e
                                _                -> Nothing

  tr (ConPat g _as) = Just (Left g)
  tr (LitPat l)     = Just (Right l)
  tr Default        = Nothing

  lk (Left g')  (ConPat g _as) = g == g'
  lk (Right l') (LitPat l)     = l == l'
  lk _          _              = False

  su (ConPat _ as) (ConPat _ bs) e = foldr (uncurry unsafeSubst) e (map Lcl bs `zip` as)
  su _ _ e = e

usePoints :: Eq a => a -> Expr a -> [(Expr a,Expr a -> Expr a)]
usePoints x e =
  case e of
    Let y l r
      | x `F.notElem` l -> rebuild (\ r' -> Let y l  r') (usePoints x r)
      | x `F.notElem` r -> rebuild (\ l' -> Let y l' r)  (usePoints x l)

    Match e brs
      | all (x `F.notElem`) brs -> rebuild (\ e' -> Match e' brs) (usePoints x e)
      | x `F.notElem` e
      , [res] <-
          [ rebuild (\ rhs' -> Match e (l ++ [Case p rhs'] ++ r))
                    (usePoints x rhs)
          | (l,Case p rhs,r) <- cursor brs
          , and [ x `F.notElem` b | b <- l ++ r ]
          ]
      -> res

    _ -> [(e,id)]
  where
  rebuild f rks = [ (r,f . k) | (r,k) <- rks ] ++ [(e,id)]

