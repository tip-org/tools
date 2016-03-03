{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}
module Tip.Pass.AxiomatizeDatadecls where

#include "errors.h"
import Tip.Core
import Tip.Fresh
import Tip.Scope (dataTypeGlobals, GlobalInfo(..), globalType)

import Data.List (tails)
import Data.Monoid

import qualified Data.Map as M

axiomatizeDatadecls :: Name a => Bool -> Theory a -> Fresh (Theory a)
axiomatizeDatadecls ueq thy@Theory{..} =
  do thys <- mapM (trDatatype ueq) thy_datatypes
     return (mconcat (thys ++ [thy { thy_datatypes = [] }]))

trDatatype :: Name a => Bool -> Datatype a -> Fresh (Theory a)
trDatatype ueq dt@Datatype{..} =
  do let ty_args = map TyVar data_tvs

     -- X = nil | X = cons(head(X), tail(X))
     domx <- freshNamed "x"
     let doml = Local domx (TyCon data_name ty_args)
     let domain =
           Formula Assert (DataDomain data_name) data_tvs $
             mkQuant Forall [doml] $
               ors
                 [ Lcl doml ===
                     Gbl (constructor dt c ty_args)
                       :@: [ Gbl (projector dt c i ty_args) :@: [Lcl doml]
                           | i <- [0..length args-1]
                           ]
                 | c@(Constructor _ _ args) <- data_cons
                 ]
     -- head(cons(X,Y)) = X
     inj <-
       sequence
         [ do qs <- mapM freshLocal (map snd args)
              return $
                Formula Assert (DataProjection data_name) data_tvs $
                  mkQuant Forall qs $
                    Gbl (projector dt c i ty_args) :@:
                      [Gbl (constructor dt c ty_args) :@: map Lcl qs]
                    ===
                    Lcl (case drop i qs of q:_ -> q; [] -> __)
         | c@(Constructor _ _ args) <- data_cons
         , i <- [0..length args-1]
         ]

     -- nil /= cons(X,Y)
     distinct <-
       sequence
         [ do qs_k <- mapM freshLocal (map snd args_k)
              qs_j <- mapM freshLocal (map snd args_j)
              let tm_k = Gbl (constructor dt k ty_args) :@: map Lcl qs_k
              let tm_j = Gbl (constructor dt j ty_args) :@: map Lcl qs_j
              return $
                Formula Assert (DataDistinct data_name) data_tvs $
                  mkQuant Forall (qs_k ++ qs_j) $
                    tm_k =/= tm_j
         | (k@(Constructor _ _ args_k),j@(Constructor _ _ args_j)) <- diag data_cons
         ]

     return $
       declsToTheory $
           datatypeSigs dt
        ++ map AssertDecl (if ueq then inj else domain:inj ++ distinct)

datatypeSigs :: Name a => Datatype a -> [Decl a]
datatypeSigs dt@Datatype{..} =
     [ SortDecl (Sort data_name data_tvs) ]
  ++ [ SigDecl (Signature gbl (globalType gbl_info))
     | (gbl,gbl_info) <- dataTypeGlobals dt
     , case gbl_info of
         DiscriminatorInfo{} -> False
         _ -> True
     ]

diag :: [a] -> [(a,a)]
diag xs = [ (x,y) | x:ys <- tails xs, y <- ys ]

