{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}
module Tip.Pass.Lift (lambdaLift, letLift, eliminateLetRec, axiomatizeLambdas, boolOpLift) where

#include "errors.h"
import Tip.Core
import Tip.Fresh
import Tip.Utils

import Data.Char (toLower)
import Data.Either
import Data.List
import Data.Generics.Geniplate
import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import qualified Data.Map as Map
import Data.Maybe
import Tip.Pretty

type LiftM a = WriterT [Function a] Fresh

type TopLift a = Expr a -> LiftM a (Expr a)

liftTheory :: Name a => (a -> TopLift a) -> Theory a -> Fresh (Theory a)
liftTheory top thy = do
  ((thy_funcs', thy_asserts'), new_func_decls) <-
    runWriterT $ do
      thy_funcs' <-
        forM (thy_funcs thy) $ \func@Function{..} -> do
          new_body <-
            transformExprInM (top func_name) func_body
          return func { func_body = new_body }

      name <- lift $ freshNamed "formula"
      thy_asserts' <-
        forM (thy_asserts thy) $ \form@Formula{..} -> do
          new_body <-
            transformExprInM (top name) fm_body
          return form { fm_body = new_body }
      return (thy_funcs', thy_asserts')

  return thy{thy_funcs = new_func_decls ++ thy_funcs',
             thy_asserts = thy_asserts' }

lambdaLiftTop :: Name a => TopLift a
lambdaLiftTop e0 =
  case e0 of
    Lam lam_args lam_body ->
      do g_name <- lift (freshNamed "lam")
         let g_args = free e0
         let g_tvs  = freeTyVars e0
         let g_type = map lcl_type lam_args :=>: exprType lam_body
         let g = Function g_name g_tvs g_args g_type (Lam lam_args lam_body)
         tell [g]
         return (applyFunction g (map TyVar g_tvs) (map Lcl g_args))
    _ -> return e0

-- | Defunctionalization.
--
-- > f x = ... \ y -> e [ x ] ...
--
-- becomes
--
-- > f x = ... g x ...
-- > g x = \ y -> e [ x ]
--
-- where @g@ is a fresh function.
--
-- After this pass, lambdas only exist at the top level of functions.
lambdaLift :: Name a => Theory a -> Fresh (Theory a)
lambdaLift = liftTheory (const lambdaLiftTop)

letLiftTop :: Name a => TopLift a
letLiftTop e0 =
  case e0 of
    Let xl@(Local x xt) b e ->
      do let fvs = free b
         let tvs = freeTyVars b
         let xfn = Function x tvs fvs (exprType b) b
         tell [xfn]
         lift ((applyFunction xfn (map TyVar tvs) (map Lcl fvs) // xl) e)
    _ -> return e0

-- | Lift lets to the top level.
--
-- > let x = b[fvs] in e[x]
--
-- becomes
--
-- > e[f fvs]
-- > f fvs = b[fvs]
letLift :: Name a => Theory a -> Fresh (Theory a)
letLift = liftTheory (const letLiftTop)

eliminateLetRecTop :: Name a => a -> TopLift a
eliminateLetRecTop func e0 =
  case e0 of
    LetRec binds e -> do
      let
        -- Variables and typed that are in scope and should be
        -- added as parameters to the functions.
        env =
          usort (concatMap (free . func_body) binds)
          \\ usort (concatMap func_args binds)
        tyenv =
          usort (concatMap (freeTyVars . func_body) binds)
          \\ usort (concatMap func_tvs binds)
      -- A fresh set of names for the functions.
        names = map func_name binds
      newNames <- lift $ mapM (refreshNamed (varStr func)) names

      let
        find x = lookup x (zip names newNames)

        -- Transform an expression to refer to the lifted functions.
        transform =
          transformBi $ \e0 ->
          case e0 of
            (Gbl gbl@Global{..} :@: args)
              | Just new_name <- find gbl_name ->
                Gbl gbl{
                  gbl_name = new_name,
                    gbl_type =
                      gbl_type {
                        polytype_tvs  = tyenv ++ polytype_tvs gbl_type,
                        polytype_args = map lcl_type env ++ polytype_args gbl_type },
                    gbl_args =
                      map TyVar tyenv ++ gbl_args } :@:
                (map Lcl env ++ args)
            _ -> e0

        -- Transform the function declaration itself.
        transformFunc func@Function{..} =
          func {
            func_name = fromMaybe __ (find func_name),
            func_tvs  = tyenv ++ func_tvs,
            func_args = env ++ func_args,
            func_body = transform func_body }

      tell (map transformFunc binds)
      return (transform e)
    _ -> return e0

-- | Eliminate letrec.
eliminateLetRec :: Name a => Theory a -> Fresh (Theory a)
eliminateLetRec = liftTheory eliminateLetRecTop

axLamFunc :: Function a -> Maybe (Signature a,Formula a)
axLamFunc Function{..} =
  case func_body of
    Lam lam_args e ->
      let abs = Signature func_name (PolyType func_tvs (map lcl_type func_args) func_res)
          fm  = Formula Assert (Defunction func_name) func_tvs
                  (mkQuant
                    Forall
                    (func_args ++ lam_args)
                    (apply
                      (applySignature abs (map TyVar func_tvs) (map Lcl func_args))
                      (map Lcl lam_args)
                     === e))
      in  Just (abs,fm)
    _ -> Nothing


-- | Axiomatize lambdas.
--
-- > f x = \ y -> E[x,y]
--
-- becomes
--
-- > declare-fun f ...
-- > assert (forall x y . @ (f x) y = E[x,y])
axiomatizeLambdas :: forall a. Name a => Theory a -> Fresh (Theory a)
axiomatizeLambdas thy0 = do
  arrows <- fmap Map.fromList (mapM makeArrow arities)
  ats    <- fmap Map.fromList (mapM (makeAt arrows) arities)
  return $
    transformBi (eliminateArrows arrows) $
    transformBi (eliminateAts ats)
    thy {
      thy_sigs = Map.elems ats    ++ thy_sigs thy,
      thy_sorts = Map.elems arrows ++ thy_sorts thy
    }
  where
    thy =
      thy0 {
        thy_sigs = new_abs ++ thy_sigs thy0,
        thy_funcs = survivors,
        thy_asserts = new_form ++ thy_asserts thy0
      }
    (survivors,new) =
      partitionEithers
        [ maybe (Left fn) Right (axLamFunc fn)
        | fn <- thy_funcs thy0
        ]

    (new_abs,new_form) = unzip new

    arities = usort [ length args | args :=>: _ <- universeBi thy :: [Type a] ]
    makeArrow n = do
      ty <- freshNamed ("fun" ++ show n)
      tvs <- replicateM (n+1) fresh
      return (n, Sort ty tvs)
    makeAt arrows n = do
      name <- freshNamed ("apply" ++ show n)
      tvs <- mapM (freshNamed . mkTyVarName) [0..(n-1)]
      tv  <- freshNamed (mkTyVarName n)
      let Sort{..} = Map.findWithDefault __ n arrows
          ty          = TyCon sort_name (map TyVar (tvs ++ [tv]))
      return $
        (n, Signature name (PolyType (tvs ++ [tv]) (ty:map TyVar tvs) (TyVar tv)))

    eliminateArrows arrows (args :=>: res) =
      TyCon sort_name (map (eliminateArrows arrows) (args ++ [res]))
      where
        Sort{..} = Map.findWithDefault __ (length args) arrows
    eliminateArrows _ ty = ty

    eliminateAts ats (Builtin At :@: (e:es)) =
      Gbl (Global sig_name sig_type (args ++ [res])) :@:
      map (eliminateAts ats) (e:es)
      where
        args :=>: res = exprType e
        Signature{..} = Map.findWithDefault __ (length args) ats
    eliminateAts _ e = e

mkTyVarName :: Int -> String
mkTyVarName x = vars !! x
  where vars = ["a","b","c","d"] ++ ["t" ++ show i | i <- [0..]]


boolOpTop :: Name a => TopLift a
boolOpTop e0 =
  case e0 of
    Builtin x :@: es | x `elem` [And,Or,Implies] ->
      do f <- lift (freshNamed (map toLower (show x)))
         as <- lift (sequence [ (`Local` boolType) <$> fresh | _ <- es ])
         let fn = Function f [] as boolType (Builtin x :@: map Lcl as)
         tell [fn]
         return (applyFunction fn [] es)
    _ -> return e0


-- | Lifts boolean operators to the top level
--
-- replaces
--   (and r s t)
-- with
--   f r s t
-- and
--   f x y z = and x y z
--
-- Run  CollapseEqual and BoolOpToIf afterwards
boolOpLift :: Name a => Theory a -> Fresh (Theory a)
boolOpLift = liftTheory (const boolOpTop)

