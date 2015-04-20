{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}
module Tip.Lift (lambdaLift, letLift, axiomatizeLambdas) where

#include "errors.h"
import Tip
import Tip.Fresh
import Tip.Utils

import Data.Either
import Data.List
import Data.Generics.Geniplate
import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import qualified Data.Map as Map

type LiftM a = WriterT [Function a] Fresh

type TopLift a = Expr a -> LiftM a (Expr a)

liftAnywhere :: (Name a,TransformBiM (LiftM a) (Expr a) (t a)) =>
                TopLift a -> t a -> Fresh (t a,[Function a])
liftAnywhere top = runWriterT . transformExprInM top

liftTheory :: Name a => TopLift a -> Theory a -> Fresh (Theory a)
liftTheory top thy0 =
  do (Theory{..},new_func_decls) <- liftAnywhere top thy0
     return Theory{thy_func_decls = new_func_decls ++ thy_func_decls,..}

-- Defunctionalization.
--
-- Transforms
--
--    f x = ... \ y -> e [ x ] ...
--
-- into
--
--    f x = ... g x ...
--    g x = \ y -> e [ x ]
--
-- where g is a fresh function.
--
-- After this pass, lambdas only exist at the top level of functions
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

lambdaLift :: Name a => Theory a -> Fresh (Theory a)
lambdaLift = liftTheory lambdaLiftTop

-- Transforms
--
--    let x = b[fvs] in e[x]
--
-- into
--
--    e[x fvs]
--
-- +  x fvs = b[fvs]
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

letLift :: Name a => Theory a -> Fresh (Theory a)
letLift = liftTheory letLiftTop

-- Axiomatize lambdas
--
-- turns
--
--   f x = \ y -> E[x,y]
--
-- into
--
--   declare-fun f ...
--
--   assert (forall x y . @ (f x) y = E[x,y]
axLamFunc :: Function a -> Maybe (AbsFunc a,Formula a)
axLamFunc Function{..} =
  case func_body of
    Lam lam_args e ->
      let abs = AbsFunc func_name (PolyType func_tvs (map lcl_type func_args) func_res)
          fm  = Formula Assert func_tvs
                  (mkQuant
                    Forall
                    (func_args ++ lam_args)
                    (apply
                      (applyAbsFunc abs (map TyVar func_tvs) (map Lcl func_args))
                      (map Lcl lam_args)
                     === e))
      in  Just (abs,fm)
    _ -> Nothing

axiomatizeLambdas :: forall a. Name a => Theory a -> Fresh (Theory a)
axiomatizeLambdas thy0 = do
  arrows <- fmap Map.fromList (mapM makeArrow arities)
  ats    <- fmap Map.fromList (mapM (makeAt arrows) arities)
  return $
    transformBi (eliminateArrows arrows) $
    transformBi (eliminateAts ats)
    thy {
      thy_abs_func_decls = Map.elems ats    ++ thy_abs_func_decls thy,
      thy_abs_type_decls = Map.elems arrows ++ thy_abs_type_decls thy
    }
  where
    thy =
      thy0 {
        thy_abs_func_decls = new_abs ++ thy_abs_func_decls thy0,
        thy_func_decls = survivors,
        thy_form_decls = new_form ++ thy_form_decls thy0
      }
    (survivors,new) =
      partitionEithers
        [ maybe (Left fn) Right (axLamFunc fn)
        | fn <- thy_func_decls thy0
        ]

    (new_abs,new_form) = unzip new

    arities = usort [ length args | args :=>: _ <- universeBi thy :: [Type a] ]
    makeArrow n = do
      ty <- freshNamed ("fun" ++ show n)
      return (n, AbsType ty (n+1))
    makeAt arrows n = do
      name <- freshNamed ("apply" ++ show n)
      tvs <- mapM (freshNamed . mkTyVarName) [0..(n-1)]
      tv  <- freshNamed (mkTyVarName n)
      let AbsType{..} = Map.findWithDefault __ n arrows
          ty          = TyCon abs_type_name (map TyVar (tvs ++ [tv]))
      return $
        (n, AbsFunc name (PolyType (tvs ++ [tv]) (ty:map TyVar tvs) (TyVar tv)))

    eliminateArrows arrows (args :=>: res) =
      TyCon abs_type_name (map (eliminateArrows arrows) (args ++ [res]))
      where
        AbsType{..} = Map.findWithDefault __ (length args) arrows
    eliminateArrows _ ty = ty

    eliminateAts ats (Builtin At :@: (e:es)) =
      Gbl (Global abs_func_name abs_func_type (args ++ [res])) :@:
      map (eliminateAts ats) (e:es)
      where
        args :=>: res = exprType e
        AbsFunc{..} = Map.findWithDefault __ (length args) ats
    eliminateAts _ e = e
