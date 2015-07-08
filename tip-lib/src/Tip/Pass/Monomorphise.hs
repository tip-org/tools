{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
module Tip.Pass.Monomorphise (monomorphise,monomorphise',Verbosity(..)) where

#include "errors.h"
import Tip.Utils.Specialiser hiding (Rule,Expr)
import qualified Tip.Utils.Specialiser as S
import Tip.Utils
import Tip.Fresh
import Tip.Core hiding (Expr)
import qualified Tip.Core as Tip

import qualified Data.Foldable as F

import Control.Arrow (second)

import Tip.Pretty
import Text.PrettyPrint
import Tip.Pretty.SMT

import Control.Monad
import Control.Monad.Writer

import Data.Generics.Geniplate

import Data.List (groupBy,sort)
import Data.Function (on)

import Debug.Trace

trListTYPE :: (Type a -> Type a) -> [((a,[Type a]),a)] -> [((a,[Type a]),a)]
trListTYPE = undefined
return []
trList :: (Type a -> Type a) -> [((a,[Type a]),a)] -> [((a,[Type a]),a)]
trList = $(genTransformBi 'trListTYPE)

type Expr a = S.Expr (Con a) a
type Rule a = S.Rule (Con a) a

monomorphise :: forall a . Name a => Verbosity -> Theory a -> Fresh (Theory a)
monomorphise verbosity = fmap (fmap unPPVar) . monomorphise' verbosity . fmap PPVar

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

monomorphise' :: forall a . (Name a,Pretty a) => Verbosity -> Theory a -> Fresh (Theory a)
monomorphise' _verbosity thy | monomorphicThy thy = return thy
monomorphise' verbosity  thy = do
    let init_fuel = 2
        ds = theoryDecls thy

    prio_rules <-
      sequence
        [ do prio_rules <- declToRule init_fuel decl
             return [ (prio,(decl,rule)) | (prio,rule) <- prio_rules ]
        | decl <- theoryDecls thy
        ]

    let rules = map snd (usort (concat prio_rules))

    let insts0 :: [(Decl a,Subst a Void (Con a))]
        loops :: [(Decl a,Rule a)]
        (insts0,weaks,loops) = specialiseWithWeakener' (\ _ -> weaken) rules

    let insts = usort (map (second removeFuels) insts0)

    when (verbosity == Verbose) $
      do traceM (show ("rules:" $\ pp
           [ (g, map snd rls)
           | rls@((g,_):_) <- groupBy ((==) `on` fst) (sort rules)
           ]))
         traceM (show ("weaks:" $\ pp weaks))
         traceM (show ("loops:" $\ pp loops))
         traceM (show ("insts:" $\ pp insts))

    if null loops
      then do
        (insts',renames) <- runWriterT (mapM (uncurry renameDecl) insts)
        return $ renameWith (renameRenames renames) (declsToTheory insts')
      else return thy

removeFuels :: Subst a Void (Con a) -> Subst a Void (Con a)
removeFuels = filter $ \ (_,p) -> case p of Con Suc [_] -> False
                                            _           -> True

weaken :: Rule a -> Maybe (Rule a)
weaken (pre :==> Con c (Con Suc [n]:rest)) = Just (pre :==> Con c (n:rest))
weaken _ = Nothing

fuelTm :: Int -> Expr a
fuelTm 0 = Con Zero []
fuelTm n = fuelSuc (fuelTm (n-1))

fuelSuc :: Expr a -> Expr a
fuelSuc x = Con Suc [x]

freshFuel :: Name a => Fresh (Expr a)
freshFuel = do i <- fresh
               n <- freshNamed ("n" ++ show (i :: Int))
               return (Var n)

data Con a = Pred a | TCon a | TyArr | TyBun BuiltinType | This a | Suc | Zero | Min
  deriving (Eq,Ord,Show)

instance Pretty a => Pretty (Con a) where
  pp (Pred x)   = "Pred" <+> pp x
  pp (TCon x)   = "TCon" <+> pp x
  pp TyArr      = "=>"
  pp (TyBun bu) = ppBuiltinType bu
  pp (This x)   = "This" <+> pp x
  pp Suc        = "s"
  pp Zero       = "z"
  pp Min        = "min"

trType :: Name a => Maybe (Expr a) -> Type a -> Fresh (Expr a)
trType mfl (TyCon tc ts) = do f <- maybe freshFuel return mfl
                              (Con (TCon tc) . (f:)) <$> mapM (trType mfl) ts
trType mfl (ts :=>: tr)      = Con TyArr <$> mapM (trType mfl) (ts ++ [tr])
trType mfl (TyVar x)         = return (Var x)
trType mfl (BuiltinType bun) = return (Con (TyBun bun) [])

toType :: Expr a -> Type a
toType (Con (TCon tc) ts)   = TyCon tc (map toType (drop 1 ts))
toType (Con TyArr ts)       = map toType (init ts) :=>: toType (last ts)
toType (Var x)              = TyVar x
toType (Con (TyBun bun) []) = BuiltinType bun

close :: Expr a -> Closed (Con a)
close = fmap (error "contains variables")

preludeRules :: forall a . Name a => Int -> Theory a -> Fresh [Rule a]
preludeRules maxfuel thy =
  do let mins =
            [ [] :==> Con Min [fuelTm a,fuelTm b,fuelTm (a `min` b)]
            | a <- [0..maxfuel]
            , b <- [0..maxfuel]
            ]

     arrows <-
       sequence
         [ do as <- mapM (fmap Var . const fresh) (args ++ [res])
              return [ [Con TyArr as] :==> a | a <- as ]
         | args :=>: res :: Type a <- universeBi thy
         ]

     return (concat arrows)

sigRule :: Name a => a -> [a] -> [Type a] -> Type a -> Fresh [(Prio,Rule a)]
sigRule f tvs args res =
  do fuel <- fuelSuc <$> freshFuel
     sequence
       [ do tt <- trType (Just fuel) t
            return (Dependency,[Con (Pred f) (fuel:map Var tvs)] :==> tt)
       | t <- res : args
       ]

data Prio
    = Prelude
    | Seed
    | Dependency
    | Definition
    | Safe
    | Enthusiastic
  deriving (Eq,Ord,Show,Bounded,Enum)

-- Returns (fresh) fuels, and then the globals
-- use them as preconditions
exprGlobalRecords :: forall a . Name a => Tip.Expr a -> Fresh [(Expr a,Expr a)]
exprGlobalRecords e =
  sequence
    [ do fuel <- fuelSuc <$> freshFuel
         args <- mapM (trType Nothing {- (Just fuel) -}) gbl_args
         return (fuel, Con (Pred gbl_name) (fuel:args))
    | Global{..} <- universeBi e
    ]

-- to be used as postconditions
seedGlobalRecords :: forall a . Name a => Expr a -> Tip.Expr a -> Fresh [Expr a]
seedGlobalRecords fuel e =
  sequence
    [ Con (Pred gbl_name) . (fuel:) <$> mapM (trType (Just fuel)) gbl_args
    | Global{..} <- universeBi e
    ]


-- always write rules with a successor on the rhs, it can be lowered later
-- simple!
declToRule :: Name a => Int -> Decl a -> Fresh [(Prio,Rule a)]
declToRule fuel d =
  case d of
    SortDecl (Sort d tvs) ->
      do n <- fuelSuc <$> freshFuel
         let s = Con (TCon d) (n:map Var tvs)
         return $
           [(Definition, [s] :==> s)] ++
           [(Dependency, [s] :==> Var tv) | tv <- tvs]


    SigDecl (Signature f (PolyType tvs args res)) -> sigRule f tvs args res

    AssertDecl (Formula Prove tvs body) ->
      do seeds <- seedGlobalRecords (fuelTm fuel) body
         return [ (Seed, [] :==> r) | r <- seeds ]
    DataDecl (Datatype tc tvs cons) ->
      do sigs <-
           sequence $
             [ sigRule k tvs (map snd args) (TyCon tc (map TyVar tvs))
             | Constructor k _ args <- cons
             ] ++
             [ sigRule d tvs (map snd args) boolType
             | Constructor _ d args <- cons
             ] ++
             [ sigRule proj tvs [TyCon tc (map TyVar tvs)] res_ty
             | Constructor _ _ args <- cons
             , (proj,res_ty) <- args
             ]
         fuel <- fuelSuc <$> freshFuel
         let tcon x = Con (TCon x) (fuel:map Var tvs)
             pred x = Con (Pred x) (fuel:map Var tvs)
         return $
           concat sigs ++
           [ (Dependency, [tcon tc] :==> (pred f))
           | Constructor k d args <- cons
           , f <- [k,d] ++ map fst args
           ]
         -- what about the types appearing as arguments in the data type?
         -- data K a = L (K (a,a)) | S a
         -- here we need K a -> (a,a)

    FuncDecl (Function f tvs args res body) ->
      do let ff fuel = Con (Pred f) (fuel:map Var tvs)
         sig <- sigRule f tvs (map lcl_type args) res
         deps <- dependencies body ff
         cls <- cloning tvs body ff
         return $ sig ++ deps ++ cls

    AssertDecl (Formula Assert tvs body) ->
      do l <- freshNamed "L"
         let ll fuel = Con (This l) (fuel:map Var tvs)
         deps <- dependencies body ll
         cls <- cloning tvs body ll
         return $ deps ++ cls

mins :: Name a => [Expr a] -> Fresh (Expr a,[Expr a])
mins []       = ERROR("No precondition")
mins [m]      = return (m,[])
mins (m:n:ns) = do (nns,cond) <- mins (n:ns)
                   o <- fuelSuc <$> freshFuel
                   return (o,Con Min [m,nns,o]:cond)

dependencies :: Name a => Tip.Expr a -> (Expr a -> Expr a) -> Fresh [(Prio,Rule a)]
dependencies body mk_lhs =
  do fuel <- fuelSuc <$> freshFuel
     seeds <- seedGlobalRecords fuel body
     return [ (Dependency,[mk_lhs fuel] :==> gbl) | gbl <- seeds ]

cloning :: Name a => [a] -> Tip.Expr a -> (Expr a -> Expr a) -> Fresh [(Prio,Rule a)]
cloning tvs body mk_rhs =
  {- (++) <$> safeCloning body mk_rhs
       <*> -} enthusiasticCloning tvs body mk_rhs

safeCloning :: Name a => Tip.Expr a -> (Expr a -> Expr a) -> Fresh [(Prio,Rule a)]
safeCloning body mk_rhs =
  do (gbl_fuels,gbl_recs) <- unzip <$> exprGlobalRecords body
     (fuel,min_pre) <- mins gbl_fuels
     return $ [(Safe,(gbl_recs ++ min_pre) :==> mk_rhs fuel)]

enthusiasticCloning :: Name a => [a] -> Tip.Expr a -> (Expr a -> Expr a) -> Fresh [(Prio,Rule a)]
enthusiasticCloning tvs body mk_rhs =
  do gbls <- exprGlobalRecords body
     return
        [ (Enthusiastic,[gbl_rec] :==> mk_rhs gbl_fuel)
        | (gbl_fuel,gbl_rec) <- gbls
        , and [ tv `F.elem` gbl_rec | tv <- tvs ]
        ]
     -- TODO: add duplets and triplets to cover

{-
        * SEEDS: Ground instances from the definition. Starts at some fuel, like
                 1, 2 or 3.

        * DEPS:  Definitions. These only get fuels with direct
                 polymorphic recursion

        * SAFE:  If everything that is required is active, also activate this

        * ENTH:  If enough things to cover the precondition is active,
                 also activate this (very enthusiastic)

    If a definition comes back with fuel 0, we could call the parametric
    version and keep that around.  But that's not directly going to work
    the type of arguments are a mix of instantiated and polymorphic data
    types, so we could just let this module abstract them immediately!
    (lemmas are removed, data types and functions are given abstract sorts
    or abstract signatures.)

-}

renameRenames :: Ord a => [((a,[Type a]),a)] -> [((a,[Type a]),a)]
renameRenames su =
    let su' = trList (tyRename su) su
        su2 = usort (su ++ su')
    in  if su == su2 then su else renameRenames su2

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

renameDecl :: forall a . Name a => Decl a -> Subst a Void (Con a) -> WriterT [((a,[Type a]),a)] Fresh (Decl a)
renameDecl d su = case d of
    SortDecl (Sort s tvs)  -> do
        s' <- rename tvs s
        return (SortDecl (Sort s' []))
    SigDecl (Signature f pt@(PolyType tvs _ _)) -> do
        f' <- rename tvs f
        let (args',res) = applyPolyType pt (ty_args tvs)
        return (SigDecl (Signature f' (PolyType [] args' res)))
    AssertDecl (Formula r tvs b) ->
        return (ty_inst tvs (AssertDecl (Formula r [] b)))

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
  ty_args tvs = [ toType (fmap absurd e) | tv <- tvs, let Just e = lookup tv su ]

  ty_inst :: [a] -> Decl a -> Decl a
  ty_inst tvs d = applyTypeInDecl tvs (ty_args tvs) d

  rename :: [a] -> a -> WriterT [((a,[Type a]),a)] Fresh a
  -- rename [] f = return f
  rename tvs f = do
    f' <- lift (refresh f)
    tell [((f,ty_args tvs),f')]
    return f'

