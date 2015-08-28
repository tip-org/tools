{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module Tip.Pass.Monomorphise where

import Tip.Utils.Specialiser
import Tip.Utils
import Tip.Fresh
import Tip.Core hiding (Expr)
import qualified Tip.Core as Tip

import qualified Data.Foldable as F

import Tip.Pretty
import Text.PrettyPrint
import Tip.Pretty.SMT

import Control.Monad
import Control.Monad.Writer

import Data.Generics.Geniplate

import Data.List (union)

import Debug.Trace

trListTYPE :: (Type a -> Type a) -> [((a,[Type a]),a)] -> [((a,[Type a]),a)]
trListTYPE = undefined
return []
trList :: (Type a -> Type a) -> [((a,[Type a]),a)] -> [((a,[Type a]),a)]
trList = $(genTransformBi 'trListTYPE)

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

monomorphise' :: forall a . (Name a,Pretty a) => Bool -> Theory a -> Fresh (Theory a)
monomorphise' _verbose thy | monomorphicThy thy = return thy
monomorphise'  verbose thy = do
    let ds = theoryDecls thy
        insts :: [(Decl a,Subst a Void (Con a))]
        loops :: [Decl a]
        rules = [ (d,declToRule True d) | d <- ds ]
        (insts,loops) = specialise rules
    when verbose $
      do traceM (show ("rules:" $\ pp rules))
         traceM (show ("loops:" $\ pp loops))
         traceM (show ("insts:" $\ pp insts))
    if null loops
      then do
        (insts',renames) <- runWriterT (mapM (uncurry renameDecl) insts)
        return $ renameWith (renameRenames renames) (declsToTheory insts')
      else return thy

exprGlobalRecords :: forall a . Ord a => Tip.Expr a -> [Expr (Con a) a]
exprGlobalRecords e = usort $
    [ Con (Pred gbl_name) (map trType gbl_args)
    | Global{..} <- universeBi e
    ]

-- why are you going to use exprTypeRecords?
exprTypeRecords :: forall a . Ord a => Tip.Expr a -> [Expr (Con a) a]
exprTypeRecords e = usort $
    [ t
    | Lcl (Local{..}) :: Tip.Expr a <- universeBi e
    , t <- typeRecords lcl_type
    ]
    ++
    -- need this for nils lying around
    -- (another fix is to make list(a) or cons(a) imply a
    [ t
    | g@Global{..} :: Tip.Global a <- universeBi e
    -- , let (as,res) = gblType g
    -- , inst_ty <- res:as
    , inst_ty <- gbl_args -- NB: looks at the instantiated global type
    , t <- typeRecords inst_ty
    ]



-- We're traversing right now to get all the TyArr that's needed
-- Otherwise it's enough to only use the top + add the rules
-- =>(a,b) -> a, b
typeRecords :: forall a . Ord a => Tip.Type a -> [Expr (Con a) a]
typeRecords t = usort $
    [ Con (TCon ty) (map trType args)
    | TyCon ty args :: Type a <- universeBi t
    ] ++
    [ Con TyArr (map trType (args ++ [res]))
    | args :=>: res :: Type a <- universeBi t
    ]

exprRecords :: forall a . Ord a => Tip.Expr a -> [Expr (Con a) a]
exprRecords e = usort $ exprGlobalRecords e ++ exprTypeRecords e

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
  rename [] f = return f
  rename tvs f = do
    f' <- lift (refresh f)
    tell [((f,ty_args tvs),f')]
    return f'

data Con a = Pred a | TCon a | TyArr | TyBun BuiltinType | Dummy
  deriving (Eq,Ord,Show)

instance Pretty a => Pretty (Con a) where
  pp (Pred x)   = "Pred" <+> pp x
  pp (TCon x)   = "TCon" <+> pp x
  pp TyArr      = "=>"
  pp (TyBun bu) = ppBuiltinType bu
  pp Dummy      = "dummy"

trType :: Type a -> Expr (Con a) a
trType (TyCon tc ts)     = Con (TCon tc) (map trType ts)
trType (ts :=>: tr)      = Con TyArr (map trType ts ++ [trType tr])
trType (TyVar x)         = Var x
trType (BuiltinType bun) = Con (TyBun bun) []

toType :: Expr (Con a) a -> Type a
toType (Con (TCon tc) ts)   = TyCon tc (map toType ts)
toType (Con TyArr ts)       = map toType (init ts) :=>: toType (last ts)
toType (Var x)              = TyVar x
toType (Con (TyBun bun) []) = BuiltinType bun

close :: Expr (Con a) a -> Closed (Con a)
close = fmap (error "contains variables")

sigRule :: Ord a => a -> [a] -> [Type a] -> Type a -> [Rule (Con a) a]
sigRule f tvs args res = usort $
    [ Rule [Con (Pred f) (map Var tvs)] t
    | t0 <- res : args, t <- typeRecords t0
    ]

declToRule :: Ord a => Bool -> Decl a -> [Rule (Con a) a]
declToRule enthusiastic_function_inst d = usort $ case d of

    SortDecl (Sort d tvs) ->
        [Rule [Con (TCon d) (map Var tvs)] (Con Dummy [])]

    SigDecl (Signature f (PolyType tvs args res)) ->
        sigRule f tvs args res

    AssertDecl (Formula Prove tvs b) ->
        map (Rule []) (Con Dummy []:exprRecords b)

    AssertDecl (Formula Assert tvs b) ->
        -- careful instantiation
        [ Rule (exprGlobalRecords b) e
        | e <- Con Dummy []:exprTypeRecords b
        ]

    DataDecl (Datatype tc tvs cons) ->
        let tcon x = Con (TCon x) (map Var tvs)
            pred x = Con (Pred x) (map Var tvs)
        in  concat [ sigRule k tvs (map snd args) (TyCon tc (map TyVar tvs))
                   | Constructor k _ args <- cons
                   ]
            ++ [ Rule [tcon tc] (pred f)
               | Constructor k d args <- cons
               , f <- [k,d] ++ map fst args
               ]

    FuncDecl (Function f tvs args res body) ->
        [ Rule (exprGlobalRecords body) (Con (Pred f) (map Var tvs))
        | enthusiastic_function_inst ] ++
        sigRule f tvs (map lcl_type args) res ++
        map (Rule [Con (Pred f) (map Var tvs)]) (exprGlobalRecords body)

