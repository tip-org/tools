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
import Tip.Core hiding (Expr, Head, (:=>:))
import qualified Tip.Core as Tip

import Tip.Scope (dataTypeGlobals, globalType)

import qualified Data.Foldable as F

import Tip.Pretty
import Text.PrettyPrint
import Tip.Pretty.SMT

import Control.Monad
import Control.Monad.Writer

import Data.Generics.Geniplate

import Data.Either
import Data.Maybe

import Debug.Trace

--------------------------------------------------------------------------------
-- Record expressions

data Head a = Fun a | Con a | Arrow Int | Type | Bun BuiltinType | Decl (Decl a) | Fuel
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type Rule' a = Rule (Expr' a)
type Expr' a = Expr a (Head a)

instance (PrettyVar a,Pretty a) => Pretty (Head a) where
  pp (Fun x)  = pp x
  pp (Con x)  = pp x
  pp Arrow{}  = "=>"
  pp Type     = "type"
  pp (Bun bu) = ppBuiltinType bu
  pp (Decl d) = text ("Decl_" ++ declName d)
  pp Fuel     = "fuel"

declName (SortDecl Sort{sort_name = t}) = varStr t
declName (SigDecl Signature{sig_name = t}) = varStr t
declName (DataDecl Datatype{data_name = t}) = varStr t
declName (FuncDecl Function{func_name = t}) = varStr t
declName (AssertDecl (Formula r i _ _)) = show r ++ "_" ++ show i

trType :: Type a -> Expr' a
trType (TyCon tc ts)     = App (Con tc) (map trType ts)
trType (ts Tip.:=>: tr)      = App (Arrow (length ts)) (map trType ts ++ [trType tr])
trType (BuiltinType bun) = App (Bun bun) []
trType (TyVar x)         = Var x

toType :: Expr x (Head a) -> Type a
toType (App (Con tc) ts)  = TyCon tc (map toType ts)
toType (App (Arrow _) ts) = map toType (init ts) Tip.:=>: toType (last ts)
toType (App (Bun bun) []) = BuiltinType bun
toType _                  = error "Tip.Pass.Monomorphise.toType: variable or strange type"

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
    [ App Type [trType t]
    | Local _ t :: Tip.Local a <- usort (universeBi e)
    ]

exprRecords :: Ord a => Tip.Expr a -> [Expr' a]
exprRecords e = usort $ exprGlobalRecords e ++ exprTypeRecords e

--------------------------------------------------------------------------------
-- Fuels

transExpr :: (Expr c a -> Expr c a) -> Expr c a -> Expr c a
transExpr = transformBi

transRule :: (Expr' a -> Expr' a) -> Rule' a -> Rule' a
transRule = transformBi

transRules :: (Expr c a -> Expr c a) -> [Rule (Expr c a)] -> [Rule (Expr c a)]
transRules = transformBi

removeFuel :: Expr v (Head a) -> Expr v (Head a)
removeFuel (App Fuel [e]) = removeFuel e
removeFuel e = e

fuel :: Expr' a -> Expr' a
fuel e = App Fuel [e]

lowerFuel :: Rule' a -> Rule' a
lowerFuel (t :=>: e) = fuel t :=>: lowerFuel e
lowerFuel (Fact e) = Fact e

complete :: a -> Int -> [Rule' a] -> [Rule' a]
complete var n rules =
  [App Fuel [Var var] :=>: Fact (Var var)] ++
  concatMap (complete1 n) rules
  where
    complete1 0 rule = [rule]
    complete1 n rule =
      rule:complete1 (n-1) (transRule fuel rule)

--------------------------------------------------------------------------------
-- Rules

sigRules :: Name a => Maybe (a, [Type a]) -> Signature a -> [Rule' a]
sigRules polyrec (Signature f _ (PolyType tvs args res)) =
  usort [ maybePoly (App (Fun f) (map Var tvs)) :=>: Fact (App Type [trType t])
        | t <- res : args
        , let maybePoly =
                case polyrec of
                  Just (x, ty) | x `elem` tyCons t && t /= TyCon x ty -> fuel
                  _ -> id
        ]

declRules :: forall a. Name a => [Expr' a] -> (a -> Maybe [a]) -> Decl a -> [Rule' a]
declRules skolems polyrec d =
  usort $
  case d of
    SortDecl (Sort t _ tvs) ->
         [ App Type [App (Con t) (map Var tvs)] :=>: Fact (App (Decl d) (map Var tvs)) ]
      ++ [ App Type [App (Con t) (map Var tvs)] :=>: Fact (App Type [Var tv]) | tv <- tvs ]
      ++ skolemise tvs (\tvs -> Fact (App Type [App (Con t) tvs]))

    SigDecl sig@(Signature f _ pt@(PolyType tvs _ _)) ->
         [ App (Fun f) (map Var tvs) :=>: Fact (App (Decl d) (map Var tvs)) ]
      ++ sigRules Nothing sig
      ++ skolemise tvs (\tvs -> Fact (App (Fun f) tvs))

    DataDecl dt@(Datatype t _ tvs cons) ->
         [ App Type [App (Con t) (map Var tvs)] :=>: Fact (App (Decl d) (map Var tvs)) ]
      ++ [ App Type [App (Con t) (map Var tvs)] :=>: Fact (App Type [Var tv]) | tv <- tvs ]
      ++ concat
           [ [ App Type [App (Con t) (map Var tvs)]
                        :=>: Fact (App (Fun k) (map Var tvs)) ]
             ++ sigRules (Just (t, map TyVar tvs)) (Signature k [] (globalType info))
           | (k,info) <- dataTypeGlobals dt
           ]
      ++ skolemise tvs (\tvs -> Fact (App Type [App (Con t) tvs]))

    FuncDecl fn@(Function f _ tvs args _ b) ->
         [ App (Fun f) (map Var tvs) :=>: Fact (App (Decl d) (map Var tvs)) ]
      ++ [ rule (map maybeFuel (exprRecords b)) (App (Decl d) (map Var tvs)) ]
      ++ sigRules Nothing (signature fn)
      ++ safe
      ++ map lowerFuel careful
      ++ skolemise tvs (\tvs -> Fact (App (Fun f) tvs))
      where
        mgrp = polyrec f
        maybeFuel e@(App (Fun g) _)
          | g `elem` fromMaybe [] mgrp = fuel e
        maybeFuel e = e
        (careful,safe) =
          partitionEithers
            [ side $ App (Decl d) (map Var tvs) :=>: Fact r
            | r <- exprRecords b
            , let side = case (r,mgrp) of
                           (App (Fun f) _,Just grp) | f `elem` grp -> Left
                           _                                       -> Right
            ]

    AssertDecl (Formula Prove _ [] b) ->
         [ Fact (App (Decl d) []) ]
      ++ [ Fact r | r <- exprRecords b ]

    AssertDecl (Formula Prove _ (_:_) _) ->
      error "Monomorphise: cannot monomorphise with polymorphic goal, run --type-skolem-conjecture"

    AssertDecl (Formula Assert _ tvs b) ->
         [ rule (exprGlobalRecords b) (App (Decl d) (map Var tvs)) ]
      ++ [ rule
           [ rec
           | rec <- exprGlobalRecords b
           , not (F.null rec) -- has some variables in it
           ]
           (App (Decl d) (map Var tvs))
         ]
      ++ map lowerFuel [ rule pre (App (Decl d) (map Var tvs))
                       | pre <- covers [ (r,F.toList r) | r <- exprGlobalRecords b ]
                       ]
      ++ [ App (Decl d) (map Var tvs) :=>: Fact r | r <- exprRecords b ]
      ++ skolemise tvs (\tvs -> Fact (App (Decl d) tvs))
  where
    skolemise :: [a] -> ([Expr' a] -> b) -> [b]
    skolemise tvs f =
      map f (sequence (map (const skolems) tvs))

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

renameDecl :: forall a . Name a => Decl a -> [Expr Int (Head a)] -> WriterT [((a,[Type a]),a)] Fresh (Decl a)
renameDecl d su =
  case d of
    SortDecl (Sort s attrs tvs)  -> do
        s' <- rename tvs s
        return (SortDecl (Sort s' attrs []))
    SigDecl (Signature f attrs pt@(PolyType tvs _ _)) -> do
        f' <- rename tvs f
        let (args',res) = applyPolyType pt (ty_args tvs)
        return (SigDecl (Signature f' attrs (PolyType [] args' res)))
    AssertDecl (Formula r attrs tvs b) ->
        return (ty_inst tvs (AssertDecl (Formula r attrs [] b)))

    DataDecl (Datatype tc attrs tvs cons) -> do
        tc' <- rename tvs tc
        cons' <- sequence
            [ do k' <- rename tvs k
                 d' <- rename tvs d
                 args' <- sequence [ do p' <- rename tvs p; return (p',t) | (p,t) <- args ]
                 return (Constructor k' attrs d' args')
            | Constructor k attrs d args <- cons
            ]
        return (ty_inst tvs (DataDecl (Datatype tc' attrs [] cons')))

    FuncDecl fn@(Function f attrs tvs args res body) -> do
        f' <- rename tvs f
        let fn' = Function f' attrs [] args res body
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

monomorphise :: forall a . Name a => Bool -> Int -> Theory a -> Fresh (Theory a)
monomorphise verbose fuel = fmap (fmap unPPVar) . monomorphise' verbose fuel . fmap PPVar

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

specialise :: (Name a, Pretty a) => [Rule (Expr Int (Head a))] -> [(Decl a,[Expr Int (Head a)])]
specialise = usort . decls . specialiseRules
  where
  decls es =
    let s = [ (d,xs) | App Fuel [e] <- es, App (Decl d) xs <- [removeFuel e] ]
        z = [ (d',xs)
            | App (Decl d) xs <- es
            , (d,xs) `notElem` s
            , d' <-
                case d of
                  FuncDecl f   -> [SigDecl (signature f)]
                  DataDecl dt  -> [ sd | sd@SortDecl{} <- datatypeSigs dt ]
                  SigDecl{}    -> [d]
                  SortDecl{}   -> [d]
                  AssertDecl{} -> []
            ]
    in  s ++ z

monomorphise' :: forall a . (Name a,Pretty a) => Bool -> Int -> Theory a -> Fresh (Theory a)
monomorphise' _verbose fuel _thy | fuel < 0 =
  error "The number of rounds must be at least 1."
monomorphise' _verbose _fuel thy | monomorphicThy thy = return thy
monomorphise'  verbose  fuel thy =
  do let ds = theoryDecls thy
     let skolems = [ trType (TyCon sort_name []) | sort@Sort{..} <- thy_sorts thy, null sort_tvs, hasAttr skolem sort]
     var <- freshNamed "rule"
     let rules0 = usort $ concatMap (declRules skolems (polyrecursive thy)) ds
     when verbose $ traceM (show ("rules0:" $\ pp rules0))
     let rules = usort $ complete var fuel rules0
     when verbose $ traceM (show ("rules:" $\ pp rules))
     let rules' = map (fmap numberVars) rules
     -- when verbose $ traceM (show ("rules':" $\ pp rules'))
     when verbose $ traceM (show ("specialised:" $\ pp (specialiseRules rules')))
     let insts = specialise rules'
     when verbose $ traceM (show ("insts:" $\ pp insts))
     (insts',renames) <- runWriterT (mapM (uncurry renameDecl) insts)
     return $ renameWith (renameRenames renames) (declsToTheory insts')

