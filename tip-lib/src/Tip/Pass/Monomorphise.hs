{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module Tip.Pass.Monomorphise where

import Tip.Utils.Horn
import Tip.Utils.SetCover
import Tip.Pass.UniqLocals
import Tip.Pass.AxiomatizeDatadecls (datatypeSigs)
import Tip.Utils
import Tip.Fresh
import Tip.Core hiding (Expr, Head)
import qualified Tip.Core as Tip

import Tip.Scope (dataTypeGlobals, GlobalInfo(..), globalType)

import qualified Data.Foldable as F

import Tip.Pretty
import Text.PrettyPrint
import Tip.Pretty.SMT

import Control.Monad
import Control.Monad.Writer

import Data.Generics.Geniplate

import Data.List (union)
import Data.Maybe (catMaybes)
import Data.Either

import Debug.Trace

--------------------------------------------------------------------------------
-- Record expressions

data Head a = Fun a | Con a | Arrow Int | Bun BuiltinType | Decl (Decl a) | S | Z | N -- ^ preliminary fuel variable
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type Rule' a = Rule (Head a) a

type Expr' a = Expr (Head a) a

instance (PrettyVar a,Pretty a) => Pretty (Head a) where
  pp (Fun x)  = pp x
  pp (Con x)  = pp x
  pp Arrow{}  = "=>"
  pp (Bun bu) = ppBuiltinType bu
  pp (Decl d) = text ("Decl_" ++ declName d)
  pp S        = ":s"
  pp Z        = ":z"
  pp N        = "n"

declName (SortDecl (Sort t _)) = varStr t
declName (SigDecl (Signature t _)) = varStr t
declName (DataDecl (Datatype t _ _)) = varStr t
declName (FuncDecl (Function t _ _ _ _)) = varStr t
declName (AssertDecl (Formula r i _ _)) = show r ++ "_" ++ show (fmap (const ()) i)

trType :: Type a -> Expr' a
trType (TyCon tc ts)     = App (Con tc) (map trType ts)
trType (ts :=>: tr)      = App (Arrow (length ts)) (map trType ts ++ [trType tr])
trType (BuiltinType bun) = App (Bun bun) []
trType (TyVar x)         = Var x

toType :: Expr (Head a) x -> Type a
toType (App (Con tc) ts)  = TyCon tc (map toType ts)
toType (App (Arrow _) ts) = map toType (init ts) :=>: toType (last ts)
toType (App (Bun bun) []) = BuiltinType bun
toType (Var _)            = error "Tip.Pass.Monomorphise.toType: variable!"

--------------------------------------------------------------------------------
-- Records

exprGlobalRecords :: forall a . Ord a => Tip.Expr a -> [Expr' a]
exprGlobalRecords e =
  usort
    [ App (Fun gbl_name) (map trType gbl_args)
    | Global{..} <- usort (universeBi e)
    ]

exprTypeRecords :: forall a . Ord a => Tip.Expr a -> [Expr' a]
exprTypeRecords e =
  usort
    [ trType lcl_type
    | Lcl (Local{..}) :: Tip.Expr a <- usort (universeBi e)
    ]

exprRecords :: Ord a => Tip.Expr a -> [Expr' a]
exprRecords e = usort $ exprGlobalRecords e ++ exprTypeRecords e

--------------------------------------------------------------------------------
-- Fuels

fuelExpr :: Int -> Expr' a
fuelExpr 0 = App Z []
fuelExpr n = fuelSucc (fuelExpr (n-1))

fuelSucc :: Expr' a -> Expr' a
fuelSucc e = App S [e]

fuelN :: Expr' a
fuelN = App N []

transExpr :: (Expr c a -> Expr c a) -> Expr c a -> Expr c a
transExpr = transformBi

transRule :: (Expr' a -> Expr' a) -> Rule' a -> Rule' a
transRule = transformBi

transRules :: (Expr c a -> Expr c a) -> [Rule c a] -> [Rule c a]
transRules = transformBi

removeFuels :: Expr c a -> Expr c a
removeFuels = transExpr k
  where
  k (App h es) = App h (drop 1 es)
  k (Var x)    = Var x

naked :: Expr c a -> Bool
naked Var{}      = False
naked (App _ es) = any variable es

variable :: Expr c a -> Bool
variable Var{}      = True
variable (App _ es) = any variable es

constFuel :: Expr' a -> Expr (Head a) a -> Expr (Head a) a
constFuel fuel (App h es) = App h (fuel:es)
constFuel _    (Var x)    = Var x

nakedFuel :: Expr' a -> Expr' a -> Expr' a -> Expr' a
nakedFuel nfuel ofuel (App h es) | any naked es = App h (nfuel:es)
                                 | otherwise    = App h (ofuel:es)
nakedFuel _ _         (Var x) = Var x


retainFuel :: [Rule' a] -> [Rule' a]
retainFuel rs = transRules (constFuel fuelN) rs

guardFuel :: [Rule' a] -> [Rule' a]
guardFuel rs = transRules (nakedFuel fuelN (fuelSucc fuelN)) rs

lowerFuel :: [Rule' a] -> [Rule' a]
lowerFuel = map go
  where
  go (l :=> r) = transExpr (constFuel (fuelSucc fuelN)) l :=> go r
  go (Fin e)   = Fin (transExpr (constFuel fuelN) e)

debumpFuel :: Expr' a -> [Rule' a]
debumpFuel e = lowerFuel [e :=> Fin e]

groundFuel :: Int -> [Rule' a] -> [Rule' a]
groundFuel n = transRules (constFuel (fuelExpr n))

realFuel :: Name a => Rule' a -> Fresh (Rule' a)
realFuel e =
  do n <- freshNamed "n"
     let k (App N []) = Var n
         k e          = e
     return (transRule k e)

--------------------------------------------------------------------------------
-- Rules

sigRules :: Name a => Signature a -> [Rule' a]
sigRules (Signature f (PolyType tvs args res)) =
     retainFuel
       (usort [ App (Fun f) (map Var tvs) :=> Fin (trType t)
              | t <- res : args
              ])
  ++ debumpFuel (App (Fun f) (map Var tvs))

declRules :: Name a => (a -> Maybe [a]) -> Int -> Decl a -> [Rule' a]
declRules polyrec fuel d =
  usort $
  case d of
    SortDecl (Sort t tvs) ->
         retainFuel [ App (Con t) (map Var tvs) :=> Fin (App (Decl d) (map Var tvs)) ]
      ++ retainFuel [ App (Con t) (map Var tvs) :=> Fin (Var tv) | tv <- tvs ]
      ++ debumpFuel (App (Con t) (map Var tvs))

    SigDecl sig@(Signature f pt@(PolyType tvs _ _)) ->
         retainFuel [ App (Fun f) (map Var tvs) :=> Fin (App (Decl d) (map Var tvs)) ]
      ++ sigRules sig

    DataDecl dt@(Datatype t tvs cons) ->
         retainFuel [ App (Con t) (map Var tvs) :=> Fin (App (Decl d) (map Var tvs)) ]
      ++ retainFuel [ App (Con t) (map Var tvs) :=> Fin (Var tv) | tv <- tvs ]
      ++ concat
           [ retainFuel [ App (Con t) (map Var tvs)
                          :=> Fin (App (Fun t) (map Var tvs)) ]
             ++ sigRules (Signature k (globalType info))
           | (k,info) <- dataTypeGlobals dt
           ]

    FuncDecl fn@(Function f tvs _ _ b) ->
         retainFuel [ App (Fun f) (map Var tvs) :=> Fin (App (Decl d) (map Var tvs)) ]
      ++ sigRules (signature fn)
      ++ retainFuel safe
      ++ lowerFuel careful
      where
        mgrp = polyrec f
        (careful,safe) =
          partitionEithers
            [ side $ App (Decl d) (map Var tvs) :=> Fin r
            | r <- exprRecords b
            , let side = case (r,mgrp) of
                           (App (Fun f) _,Just grp) | f `elem` grp -> Left
                           _                                       -> Right
            ]

    AssertDecl (Formula Prove _ tvs b) ->
      -- tvs should be empty here!!
         groundFuel fuel [ Fin (App (Decl d) (map Var tvs)) ]
      ++ groundFuel fuel [ Fin r | r <- exprRecords b ]

    AssertDecl (Formula Assert _ tvs b) ->
         retainFuel [ foldr (:=>) (Fin (App (Decl d) (map Var tvs))) (exprGlobalRecords b) ]
      ++  lowerFuel [ foldr (:=>) (Fin (App (Decl d) (map Var tvs))) pre
                    | pre <- covers [ (r,F.toList r) | r <- exprGlobalRecords b ]
                    ]
      ++ retainFuel [ App (Decl d) (map Var tvs) :=> Fin r | r <- exprRecords b ]

--------------------------------------------------------------------------------
-- Renaming

_trList :: (Type a -> Type a) -> [((a,[Type a]),a)] -> [((a,[Type a]),a)]
_trList = undefined
return []
trList :: (Type a -> Type a) -> [((a,[Type a]),a)] -> [((a,[Type a]),a)]
trList = $(genTransformBi '_trList)

renameRenames :: Ord a => [((a,[Type a]),a)] -> [((a,[Type a]),a)]
renameRenames su
  | su == su2 = su
  | otherwise = renameRenames su2
  where
  su' = trList (tyRename su) su
  su2 = usort (su ++ su')

tyRename :: Ord a => [((a,[Type a]),a)] -> Type a -> Type a
tyRename su (TyCon tc ts) | Just tc' <- lookup (tc,ts) su = TyCon tc' []
tyRename _  t0 = t0

renameWith :: Ord a => [((a,[Type a]),a)] -> Theory a -> Theory a
renameWith su = transformBi (tyRename su) . transformBi gbl
  where
  gbl (Global f (PolyType tvs args res) ts)
      | Just f' <- lookup (f,ts) su
      = let at = applyType tvs ts
        in  Global f' (PolyType [] (map at args) (at res)) []
  gbl g0 = g0

renameDecl :: forall a . Name a => Decl a -> [Expr (Head a) Int] -> WriterT [((a,[Type a]),a)] Fresh (Decl a)
renameDecl d su =
  case d of
    SortDecl (Sort s tvs)  -> do
        s' <- rename tvs s
        return (SortDecl (Sort s' []))
    SigDecl (Signature f pt@(PolyType tvs _ _)) -> do
        f' <- rename tvs f
        let (args',res) = applyPolyType pt (ty_args tvs)
        return (SigDecl (Signature f' (PolyType [] args' res)))
    AssertDecl (Formula r i tvs b) ->
        return (ty_inst tvs (AssertDecl (Formula r i [] b)))

    DataDecl (Datatype tc tvs cons) -> do
        tc' <- rename tvs tc
        cons' <- sequence
            [ do k' <- rename tvs k
                 d' <- rename tvs d
                 args' <- sequence [ do p' <- rename tvs p; return (p',t) | (p,t) <- args ]
                 return (Constructor k' d' args')
            | Constructor k d args <- cons
            ]
        return (ty_inst tvs (DataDecl (Datatype tc' [] cons')))

    FuncDecl fn@(Function f tvs args res body) -> do
        f' <- rename tvs f
        let fn' = Function f' [] args res body
        return (ty_inst tvs (FuncDecl fn'))
  where
  ty_args tvs = [ toType e | (tv,e) <- tvs `zip` su ]

  ty_inst :: [a] -> Decl a -> Decl a
  ty_inst tvs d = applyTypeInDecl tvs (ty_args tvs) d

  rename :: [a] -> a -> WriterT [((a,[Type a]),a)] Fresh a
  rename []  f = return f
  rename tvs f =
    do f' <- lift (refresh f)
       tell [((f,ty_args tvs),f')]
       return f'

--------------------------------------------------------------------------------
-- Monomorphisation

monomorphise :: forall a . Name a => Bool -> Theory a -> Fresh (Theory a)
monomorphise verbose = fmap (fmap unPPVar) . monomorphise' verbose . fmap PPVar

monomorphicThy :: Theory a -> Bool
monomorphicThy = all monomorphicDecl . theoryDecls

monomorphicDecl :: Decl a -> Bool
monomorphicDecl d =
  case d of
    DataDecl Datatype{..}  -> null data_tvs
    SortDecl Sort{..}      -> null sort_tvs
    SigDecl Signature{..}  -> null (polytype_tvs sig_type)
    FuncDecl Function{..}  -> null func_tvs
    AssertDecl Formula{..} -> null fm_tvs

specialise :: Name a => [Rule (Head a) Int] -> [(Decl a,[Expr (Head a) Int])]
specialise = usort . decls . specialiseRules
  where
  decls es =
    let s = [ (d,map removeFuels xs) | App (Decl d) (App S _:xs) <- es ]
        z = [ (d',map removeFuels xs)
            | App (Decl d) (App Z _:xs) <- es
            , (d,map removeFuels xs) `notElem` s
            , d' <-
                case d of
                  FuncDecl f   -> [SigDecl (signature f)]
                  DataDecl dt  -> [ sd | sd@SortDecl{} <- datatypeSigs dt ]
                  SigDecl{}    -> [d]
                  SortDecl{}   -> [d]
                  AssertDecl{} -> []
            ]
    in  s ++ z

monomorphise' :: forall a . (Name a,Pretty a) => Bool -> Theory a -> Fresh (Theory a)
monomorphise' _verbose thy | monomorphicThy thy = return thy
monomorphise'  verbose thy =
  do let ds = theoryDecls thy
     let rules = usort . concat . map (declRules (polyrecursive thy) 1) $ ds
     when verbose $ traceM (show ("rules:" $\ pp rules))
     rules' <- mapM (uniq (const Nothing) (const fresh) <=< realFuel) rules
     -- when verbose $ traceM (show ("rules':" $\ pp rules'))
     -- when verbose $ traceM (show ("specialised:" $\ pp (specialiseRules rules')))
     let insts = specialise rules'
     when verbose $ traceM (show ("insts:" $\ pp insts))
     (insts',renames) <- runWriterT (mapM (uncurry renameDecl) insts)
     return $ renameWith (renameRenames renames) (declsToTheory insts')

