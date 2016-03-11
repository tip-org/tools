{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tip.FreeTyCons (bindsTyCons) where

import CoreSyn
import CoreUtils (exprType)
import DataCon
import TyCon
import Id
import Type
import Var

import Data.Set (Set)
import qualified Data.Set as S

import Tip.GenericInstances
import Data.Generics.Geniplate

import Tip.Utils

bindsTyCons :: [(Var,CoreExpr)] -> [TyCon]
bindsTyCons vses = S.toList $ S.unions
  [ varTyCons v `S.union` exprTyCons e
  | (v,e) <- vses
  ]

varTyCons :: Var -> Set TyCon
varTyCons = tyTyCons . varType

tyTyCons :: Type -> Set TyCon
tyTyCons = go S.empty . expandTypeSynonyms
  where
  go visited t0
    | Just (t1,t2) <- splitFunTy_maybe t0    = S.union (go visited t1) (go visited t2)
    | Just (tc,ts) <- splitTyConApp_maybe t0 =
        -- Also consider type constructors inside original data type definition.
        -- We store that we've iterated through those constructors in order to avoid infinite
        -- loops when definition is recursive
        let ts' = if tc `S.member` visited
                      then []
                      else concatMap dataConOrigArgTys $ tyConDataCons tc
            visited' = S.insert tc visited
        in  S.insert tc $ S.unions (map (go visited') (ts ++ ts'))
    | Just (_,t) <- splitForAllTy_maybe t0   = go visited t
    | otherwise                              = S.empty

-- | For all used constructors in expressions and patterns,
--   return the TyCons they originate from
exprTyCons :: CoreExpr -> Set TyCon
exprTyCons e =
  S.unions $
    [ varTyCons x `S.union` tyTyCons t | Case _ x t _  <- universeBi e ] ++
    [ varTyCons x                      | Var x :: CoreExpr <- universeBi e ] ++
    [ tyTyCons t                       | Type t :: CoreExpr <- universeBi e ] ++
    [ S.singleton (dataConTyCon c)     | DataAlt c <- universeBi e ]
