{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module Tip.Pass.Min where

#include "errors.h"
import Tip.Pass.AxiomatizeFuncdefs
import Tip.Pass.AxiomatizeDatadecls

import Tip.Types
import Tip.Core
import Tip.Fresh
import Tip.Utils

import Tip.Pretty
import Tip.Pretty.SMT

import qualified Data.Map as M

-- assumes a monomorphic theory
minPass :: Name a => Theory a -> Fresh (Theory a)
minPass thy =
  do minsigs <-
       fmap M.fromList $ sequence
         [ do min_ <- freshNamed "min"
              return $ (t,Signature min_ (PolyType [] [t] boolType))
         | t <- theoryTypes thy
         ]
     let min_pred e = let ty = exprType e
                          msig = FROMJUST("Lost type " ++ ppRender ty ++ " on expression " ++ ppRender e)(M.lookup ty minsigs)
                      in  applySignature msig [] [e]
     thy' <- axiomatizeDatadecls (Just . min_pred)
               (axiomatizeFuncdefs2 (Just . min_pred)
                  (minAsserts min_pred thy))
     return thy'{
       thy_sigs = M.elems minsigs ++ thy_sigs thy'
     }

minAsserts :: Ord a => (Expr a -> Expr a) -> Theory a -> Theory a
minAsserts min_pred thy = thy{
   thy_asserts = concatMap (minAssert min_pred) (thy_asserts thy)
 }

-- Only works with forall quantifiers on the top level
minAssert :: Ord a => (Expr a -> Expr a) -> Formula a -> [Formula a]
minAssert min_pred fm0@(Formula role tvs (forallView -> (vs,e))) =
  case role of
    Assert -> [ Formula Assert tvs (mkQuant Forall vs (min_pred t ==> e)) | t <- tms ]
    Prove  -> [ Formula Assert tvs (mkQuant Forall vs (min_pred t))       | t <- tms ]
              ++ [ fm0 ]
  where tms = usort (terms e)

terms :: Expr a -> [Expr a]
terms (Builtin b :@: es)
  | logicalBuiltin b = concatMap terms es
terms Lcl{} = []
terms t = [t]

