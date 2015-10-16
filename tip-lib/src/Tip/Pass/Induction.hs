{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}
module Tip.Pass.Induction where

#include "errors.h"
import Tip.Core
import Tip.Fresh
import Induction.Structural

import Control.Applicative

import Data.List (find,partition)

theoryTyEnv :: Ord a => Theory a -> TyEnv (Head a) (Type a)
theoryTyEnv Theory{..} (BuiltinType Boolean) =
  do return [(Builtin (Lit (Bool b)),[]) | b <- [False,True]]

theoryTyEnv Theory{..} t =
  do TyCon tc ts <- return t
     dt@Datatype{..} <- find ((tc ==) . data_name) thy_datatypes
     return
         [ (Gbl (constructor dt c ts)
           ,[ case applyType data_tvs ts t of
                t@(TyCon tc' _) | tc == tc' -> Rec t
                t@(args :=>: _)             -> Exp t args
                t                           -> NonRec t
            | (_proj,t) <- con_args c
            ]
           )
         | c <- data_cons
         ]

trTerm :: Term (Head a) (Local a) -> Expr a
trTerm (Var lcl)   = Lcl lcl
trTerm (Con h tms) = h :@: map trTerm tms
trTerm (Fun f tms) = Builtin At :@: (Lcl f:map trTerm tms)

-- | Applies induction at the given coordinates to the first goal
induction :: (Name a,Ord a) => [Int] -> Theory a -> Fresh [Theory a]
induction coords thy@Theory{..} =
  case goal of
    Formula Prove i tvs (Quant qi Forall lcls body)
      | cs@(_:_) <- [ x | x <- coords, x >= length lcls || x < 0 ] -> error $ "Induction coordinates " ++ show cs ++ " out of bounds!"
      | otherwise ->
      do (obligs,_) <-
           unTagMapM
             (\ (v :~ _) -> refresh v)
             (subtermInduction
               (theoryTyEnv thy)
               [(lcl_name,lcl_type) | Local{..} <- lcls]
               coords)

         split_goals <-
           sequence
             [ do let attach_type env v =
                        case lookup v (env ++ sks) of
                          Just t  -> Local v t
                          Nothing -> ERROR("Lost type of variable!")
                  let replace env ts = substMany (zip lcls (map (trTerm . fmap (attach_type env)) ts)) body
                  hyps <- sequence
                            [ Quant (QuantIH i) Forall [ Local v t | (v,t) <- prenex ]
                                <$> replace prenex inst
                            | (i, (prenex, inst)) <- [0..] `zip` hyps
                            ]
                  concl <- replace [] concl
                  let body' = hyps ===> concl
                  return
                    (Formula Prove i tvs
                      (mkQuant Forall [ Local v t | (v,t) <- sks] body'))
             | Obligation sks hyps concl <- obligs
             ]

         return
           [ thy { thy_asserts = goal' : goals ++ assums }
           | goal' <- split_goals
           ]

    _ -> return [thy]
  where
  (goal:goals,assums) = partitionGoals thy_asserts

