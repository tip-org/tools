{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, CPP, RecordWildCards #-}

-- | Translation from GHC Core to the Tip IR
module Tip.CoreToTip where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader

#if __GLASGOW_HASKELL__ >= 708
import Data.ByteString (unpack)
import Data.Char (chr)
#else
import FastString (unpackFS)
#endif

import Tip as Tip

import CoreUtils as C
import CoreSyn as C

import Data.Char (ord)

import DataCon
import Literal
import Var hiding (Id)
import TyCon hiding (data_cons)
import Type as C
import GHC (dataConType)

import qualified TysPrim
import qualified PrelNames

import IdInfo

import Tip.GHCUtils (showOutputable,rmClass)
import Tip.DataConPattern
import Tip.TyAppBeta
import Tip.Id

-- | The binders in our translated expressions.
--
--   We cannot use 'Var'/'Id' because 'TyCon's do not have them,
--   and 'DataCon's does not necessarily have a unique.
--   'Name's have, just as 'Var'/'Id', a 'Unique' in them.
--
--   The types need to be remembered so we used typed
--
--   The list of var is the variables in scope

type TM a = ReaderT [Var] (Either String) a

runTM :: TM a -> Either String a
runTM m = runReaderT m []

msgUnsupportedLiteral l    = "Unsupported literal: " ++ showOutputable l
msgIllegalType t           = "Illegal type: " ++ showOutputable t
msgTypeApplicationToExpr e = "Type application to expression: " ++ showOutputable e
msgTypeExpr e              = "Type expression: " ++ showOutputable e
msgCoercionExpr e          = "Coercion expression: " ++ showOutputable e
msgCastExpr e              = "Cast expression: " ++ showOutputable e
msgHigherRankType v t      = showOutputable v ++ " has a higher-rank type: " ++ showOutputable t
msgUnificationError t tvs dc e mu =
       "Unification error on " ++ showOutputable t
       ++ "\nWhen resolving type variables " ++ showOutputable tvs
       ++ " for constructor " ++ showOutputable dc ++
       (case mu of
           Just u -> "\nObtained unifier: " ++ showOutputable u
           Nothing -> " without unifier")
       ++ "\nOriginating from expression: " ++ showOutputable e
msgNonVanillaDataCon dc tc =
       "Data constructor " ++ showOutputable dc ++

       " from type constructor " ++ showOutputable tc ++
       " is not Haskell 98!"
msgNotAlgebraicTyCon tc =
       "Type constructor " ++ showOutputable tc ++ " is not algebraic!"
msgFail s = "Internal failure: " ++ s

trTyCon :: TyCon -> Either String (Datatype Id)
trTyCon tc = do
    unless (isAlgTyCon tc) (throwError (msgNotAlgebraicTyCon tc))
    dcs <- mapM tr_dc (tyConDataCons tc)
    return Datatype
        { data_name = idFromTyCon tc
        , data_tvs  = map idFromTyVar tc_tvs
        , data_cons = dcs
        }
  where
    tc_tvs = tyConTyVars tc

    tr_dc dc = do
        unless
            (isVanillaDataCon dc)
            (throwError (msgNonVanillaDataCon dc tc))
        let dc_tys = dataConInstArgTys dc (map mkTyVarTy tc_tvs)
        ts <- mapM trType dc_tys
        return Constructor
            { con_name = idFromDataCon dc
            , con_args = ts
            }

-- | Translate a definition
trDefn :: Var -> CoreExpr -> TM (Function Id)
trDefn v e = do
    let (tvs,ty) = splitForAllTys (C.exprType e)
    ty' <- lift (trType ty)
    let (tvs',body) = collectTyBinders e
    when (tvs /= tvs') (fail "Type variables do not match in type and lambda!")
    body' <- trExpr (tyAppBeta body)
    return Function
        { func_name    = idFromVar v
        , func_tvs     = map idFromTyVar tvs
        , func_args    = []
        , func_res     = ty'
        , func_body    = body'
        }

-- | Translating variables
--
-- Need to conflate worker and wrapper data constructors otherwise
-- they might differ from case alternatives
-- (example: created tuples in partition's where clause)
-- It is unclear what disasters this might bring.
trVar :: Var -> [Tip.Type Id] -> TM (Tip.Expr Id)
trVar x tys = do
    ty <- lift (trPolyType (varType x))
    lcl <- asks (x `elem`)
    if lcl
        then case ty of
                PolyType [] tas tr -> return (Lcl (Local (idFromVar x) (tas :=>: tr)))
                _                  -> fail ("Local identifier " ++ showOutputable x ++
                                            " with forall-type: " ++ showOutputable (varType x))
        else return $ case idDetails x of
                DataConWorkId dc -> abstract $ trConstructor dc ty tys
                DataConWrapId dc -> abstract $ trConstructor dc ty tys
                _                -> global (Global (idFromVar x) ty tys FunctionNS)
    where
      abstract gbl = foldr lam body etas
        where
          body = Gbl gbl :@: map Lcl etas
          etas = zipWith (Local . Eta) [0..] args
          args = polytype_args (gbl_type gbl)
          lam lcl body = Tip.Lam [lcl] body

trConstructor :: DataCon -> PolyType Id -> [Tip.Type Id] -> Global Id
trConstructor dc ty tys = Global (idFromName $ dataConName dc) (uncurryTy ty) tys ConstructorNS
  where
    uncurryTy ty@PolyType{polytype_res = args :=>: res} =
      ty' { polytype_args = args ++ polytype_args ty' }
      where
        ty' = uncurryTy ty { polytype_res = res }
    uncurryTy ty = ty

-- | Translating expressions
--
-- GHC Core allows application of types to arbitrary expressions,
-- but this language only allows application of types to variables.
--
-- The type variables applied to constructors in case patterns is
-- not immediately available in GHC Core, so this has to be reconstructed.
trExpr :: CoreExpr -> TM (Tip.Expr Id)
trExpr e0 = case collectTypeArgs e0 of
    (C.Var x, tys) -> mapM (lift . trType) tys >>= trVar x
    (_, _:_) -> throw (msgTypeApplicationToExpr e0)
    (C.Lit l, _) -> literal <$> trLit l

    (C.App e1 e2, _) -> (\ x y -> Builtin (At 1) :@: [x,y]) <$> trExpr e1 <*> trExpr e2

    (C.Lam x e, _) -> do
        t <- lift (trType (varType x))
        e' <- local (x:) (trExpr e)
        return (Tip.Lam [Local (idFromVar x) t] e')

    (C.Let (C.NonRec v b) e, _) -> do
        vt <- lift (trType (varType v))
        b' <- trExpr b
        e' <- local (v:) (trExpr e)
        return (Tip.Let (Local (idFromVar v) vt) b' e')

    (C.Let C.Rec{} _, _) -> fail "Recursive local bindings!"
      -- need to lift them now immediately to support it
      -- which is probably a good idea anyway
      -- need to know the type variables in scope to do that

    (C.Case e x _ alts, _) -> do

        e' <- trExpr e

        let t = C.exprType e

        t' <- lift (trType t)

        let tr_alt :: CoreAlt -> TM (Tip.Case Id)
            tr_alt alt = case alt of
                (DEFAULT   ,[],rhs) -> Tip.Case Default <$> trExpr rhs

                (DataAlt dc,bs,rhs) -> do

                    let (dc_tvs,mu) = dcAppliedTo t dc
                        unif_err    = msgUnificationError t dc_tvs dc e0

                    case mu of
                        Just u -> case mapM (lookupTyVar u) dc_tvs of
                            Just tys -> do
                                tys' <- mapM (lift . trType) tys
                                bs' <- forM bs $ \ b ->
                                    (,) (idFromVar b) <$> lift (trType (varType b))
                                rhs' <- local (bs++) (trExpr rhs)
                                dct <- lift (trPolyType (dataConType dc))
                                return $ Tip.Case
                                    (ConPat (trConstructor dc dct tys') (map (uncurry Local) bs'))
                                    rhs'
                            Nothing -> throw (unif_err (Just u))
                        Nothing -> throw (unif_err Nothing)

                (LitAlt lit,[],rhs) -> do

                    -- let TyCon v [] = t'
                    lit' <- trLit lit
                    rhs' <- trExpr rhs
                    return (Tip.Case (LitPat lit') rhs')

                _ -> fail "Default or LitAlt with variable bindings"

        let scrut = Local (idFromVar x) t'

        Tip.Let scrut e' . Match (Lcl scrut) <$> local (x:) (mapM tr_alt alts)

    (C.Tick _ e, _) -> trExpr e
    (C.Type{}, _) -> throw (msgTypeExpr e0)
    (C.Coercion{}, _) -> throw (msgCoercionExpr e0)
    (C.Cast{}, _) -> throw (msgCastExpr e0)
    -- TODO:
    --     Do we need to do something about newtype casts?

collectTypeArgs :: CoreExpr -> (CoreExpr, [C.Type])
collectTypeArgs (C.App e (Type t)) = (e', tys ++ [t])
  where
    (e', tys) = collectTypeArgs e
collectTypeArgs e = (e, [])

trLit :: Literal -> TM Lit
trLit (LitInteger x _type) = return (Int x)
trLit (MachInt x)          = return (Int x)
trLit (MachInt64 x)        = return (Int x)
trLit (MachChar ch)        = return (Int (toInteger (ord ch)))
#if __GLASGOW_HASKELL__ >= 708
trLit (MachStr s) = return (String (map (chr . fromInteger . toInteger) (unpack s)))
#else
trLit (MachStr s) = return (String (unpackFS s))
#endif
trLit l           = throw (msgUnsupportedLiteral l)

trPolyType :: C.Type -> Either String (Tip.PolyType Id)
trPolyType t0 =
    let (tv,t) = splitForAllTys (expandTypeSynonyms t0)
    in  PolyType (map idFromTyVar tv) [] <$> trType (rmClass t)

throw :: String -> TM a
throw = lift . throwError

essentiallyInteger :: TyCon -> Bool
essentiallyInteger tc = tc == TysPrim.intPrimTyCon || tc == TysPrim.charPrimTyCon ||
                        tyConUnique tc == PrelNames.integerTyConKey


trType :: C.Type -> Either String (Tip.Type Id)
trType = go . expandTypeSynonyms
  where
    go t0
        | Just (t1,t2) <- splitFunTy_maybe t0    = (\ x y -> [x] :=>: y) <$> go t1 <*> go t2
        | Just (tc,[]) <- splitTyConApp_maybe t0, essentiallyInteger tc = return (BuiltinType Integer)
        | Just (tc,ts) <- splitTyConApp_maybe t0 = TyCon (idFromTyCon tc) <$> mapM go ts
        | Just tv <- getTyVar_maybe t0           = return (TyVar (idFromTyVar tv))
        | otherwise                              = throwError (msgIllegalType t0)

