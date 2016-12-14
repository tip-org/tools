{-# LANGUAGE OverloadedStrings #-}
module Tip.Parser.Convert where

import Tip.Parser.AbsTIP as A -- from A ...
import Tip.Core          as T -- ... to T
import Tip.Pretty
import Tip.Pretty.SMT

import Text.PrettyPrint
import Control.Applicative
import Control.Monad.State
import Control.Monad.Error
import Data.Foldable (foldrM)

import qualified Tip.Scope
import Tip.Scope
import Tip.Fresh

import Data.List
import Data.Function

import Data.Map (Map)
import qualified Data.Map as M

data IdKind = LocalId | GlobalId
  deriving Eq

type CM a = ScopeT Id (StateT (Map String (Id,IdKind)) Fresh) a

runCM :: CM a -> Either String a
runCM m = either (Left . show) Right $ runFresh (evalStateT (runScopeT m) M.empty)

-- | Identifiers from parsed Tip syntax
data Id = Id
  { idString :: String
  , idUnique :: Int
  , idPos    :: Maybe (Int,Int)
  -- ^ A source position of the identifier, if available
  }
  deriving Show

instance Eq Id where
  (==) = (==) `on` idUnique

instance Ord Id where
  compare = compare `on` idUnique

instance PrettyVar Id where
  varStr (Id s u _) = s -- ++ "_" ++ show u

instance Name Id where
  freshNamed n
    = do u <- fresh
         return (Id n u Nothing)
  getUnique (Id _ u _) = u

ppSym :: Symbol -> Doc
ppSym (Symbol ((x,y),s)) = text s <+> "(" <> int x <> ":" <> int y <> ")"

lkSym :: Symbol -> CM Id
lkSym sym@(Symbol (p,s)) =
  do mik <- lift $ gets (M.lookup s)
     case mik of
       Just (i,_) -> return $ i { idPos = Just p }
       Nothing    -> throwError $ "Symbol" <+> ppSym sym <+> "not bound"

addSym :: IdKind -> Symbol -> CM Id
addSym ik sym@(Symbol (p,s)) =
  do mik <- lift $ gets (M.lookup s)
     case mik of
       Just (_,GlobalId)       -> throwError $ "Symbol" <+> ppSym sym <+> "is already globally bound"
       Just _ | ik == GlobalId -> throwError $ "Symbol" <+> ppSym sym <+> "is locally bound, and cannot be overwritten by a global"
       _                       -> return ()
     u <- lift (lift fresh)
     let i = Id s u (Just p)
     lift $ modify (M.insert s (i,ik))
     return i

trDecls :: [A.Decl] -> CM (Theory Id)
trDecls [] = return emptyTheory
trDecls (d:ds) =
  do thy <- trDecl d
     withTheory thy $
       do thy_rest <- trDecls ds
          return (thy `joinTheories` thy_rest)

trDecl :: A.Decl -> CM (Theory Id)
trDecl x =
  local $
    case x of
      DeclareDatatypes tvs datatypes ->
        do -- add their types, abstractly
           forM_ datatypes $ \dt -> do
             sym <- addSym GlobalId (dataSym dt)
             tvi <- mapM (addSym LocalId) tvs
             newSort (Sort sym tvi)
           newScope $
             do tvi <- mapM (addSym LocalId) tvs
                mapM newTyVar tvi
                ds <- mapM (trDatatype tvi) datatypes
                return emptyTheory{ thy_datatypes = ds }

      DeclareSort s n ->
        do i <- addSym GlobalId s
           tvs <- lift . lift $ mapM refresh (replicate (fromInteger n) i)
           return emptyTheory{ thy_sorts = [Sort i tvs] }

      DeclareConst const_decl -> trDecl (DeclareConstPar emptyPar const_decl)

      DeclareConstPar par (ConstDecl s t) -> trDecl (DeclareFunPar par (FunDecl s [] t))

      DeclareFun        decl -> trDecl (DeclareFunPar emptyPar decl)
      DeclareFunPar par decl ->
        do d <- trFunDecl par decl
           return emptyTheory{ thy_sigs = [d] }

      DefineFun        def -> trDecl (DefineFunPar emptyPar def)
      DefineFunPar par def@(FunDef f _ _ _) ->
        do thy <- trDecl (DefineFunRecPar par def)
           let [fn] = thy_funcs thy
           when (func_name fn `elem` uses fn)
                (throwError $ ppSym f <+> "is recursive, but define-fun-rec was not used!")
           return thy

      DefineFunRec        def -> trDecl (DefineFunRecPar emptyPar def)
      DefineFunRecPar par def ->
        do sig <- trFunDecl par (defToDecl def)
           withTheory emptyTheory{ thy_sigs = [sig] } $ do
             fn <- trFunDef par def
             return emptyTheory{ thy_funcs = [fn] }

      DefineFunsRec decs bodies ->
        do -- add their correct types, abstractly
           fds <- mapM (uncurry trFunDecl . decToDecl) decs
           withTheory emptyTheory{ thy_sigs = fds } $ do
             fns <- sequence
                [ uncurry trFunDef (decToDef dec body)
                | (dec,body) <- decs `zip` bodies
                ]
             return emptyTheory{ thy_funcs = fns }

      A.Assert  role           expr -> trDecl (AssertPar role emptyPar expr)
      AssertPar role (Par tvs) expr ->
        do tvi <- mapM (addSym LocalId) tvs
           mapM newTyVar tvi
           let toRole AssertIt  = T.Assert
               toRole AssertNot = Prove
           fm <- Formula (toRole role) UserAsserted tvi <$> trExpr expr
           return emptyTheory{ thy_asserts = [fm] }

emptyPar :: Par
emptyPar = Par []

decToDecl :: FunDec -> (Par,FunDecl)
decToDecl dec = case dec of
  MonoFunDec inner -> decToDecl (ParFunDec emptyPar inner)
  ParFunDec par (InnerFunDec fsym bindings res_type) ->
    (par,FunDecl fsym (map bindingType bindings) res_type)

defToDecl :: FunDef -> FunDecl
defToDecl (FunDef fsym bindings res_type _) =
  FunDecl fsym (map bindingType bindings) res_type

trFunDecl :: Par -> FunDecl -> CM (T.Signature Id)
trFunDecl (Par tvs) (FunDecl fsym args res) =
    newScope $
      do f <- addSym GlobalId fsym
         tvi <- mapM (addSym LocalId) tvs
         mapM newTyVar tvi
         pt <- PolyType tvi <$> mapM trType args <*> trType res
         return (Signature f pt)

decToDef :: FunDec -> A.Expr -> (Par,FunDef)
decToDef dec body = case dec of
  MonoFunDec inner -> decToDef (ParFunDec emptyPar inner) body
  ParFunDec par (InnerFunDec fsym bindings res_type) ->
    (par,FunDef fsym bindings res_type body)

trFunDef :: Par -> FunDef -> CM (T.Function Id)
trFunDef (Par tvs) (FunDef fsym bindings res_type body) =
  newScope $
    do f <- lkSym fsym
       tvi <- mapM (addSym LocalId) tvs
       mapM newTyVar tvi
       args <- mapM trLocalBinding bindings
       Function f tvi args <$> trType res_type <*> trExpr body

dataSym :: A.Datatype -> Symbol
dataSym (A.Datatype sym _) = sym

trDatatype :: [Id] -> A.Datatype -> CM (T.Datatype Id)
trDatatype tvs (A.Datatype sym constructors) =
  do x <- lkSym sym
     T.Datatype x tvs <$> mapM trConstructor constructors

trConstructor :: A.Constructor -> CM (T.Constructor Id)
trConstructor (A.Constructor name@(Symbol (p,s)) args) =
  do c <- addSym GlobalId name
     is_c <- addSym GlobalId (Symbol (p,"is-" ++ s))
     T.Constructor c is_c <$> mapM (trBinding GlobalId) args

bindingType :: Binding -> A.Type
bindingType (Binding _ t) = t

-- adds to the symbol map
trBinding :: IdKind -> Binding -> CM (Id,T.Type Id)
trBinding ik (Binding s t) =
  do i <- addSym ik s
     t' <- trType t
     return (i,t')

-- adds to the symbol map and to the local scope
trLocalBinding :: Binding -> CM (Local Id)
trLocalBinding b =
  do (x,t) <- trBinding LocalId b
     let l = Local x t
     newLocal l
     return l

trLetDecls :: [LetDecl] -> A.Expr -> CM (T.Expr Id)
trLetDecls [] e = trExpr e
trLetDecls (LetDecl s expr:bs) e
  = do body <- trExpr expr
       x <- addSym LocalId s
       let l = Local x (exprType body)
       newScope $
         do newLocal l
            rest <- trLetDecls bs e
            return (T.Let l body rest)

trExpr :: A.Expr -> CM (T.Expr Id)
trExpr e0 = case e0 of
  A.Var sym ->
    do x <- lkSym sym
       ml <- gets (lookupLocal x)
       case ml of
         Just t -> return (Lcl (Local x t))
         _      -> trExpr (A.App (A.Const sym) [])

  A.As (A.Var sym) ty -> trExpr (A.As (A.App (A.Const sym) []) ty)
  A.As (A.App head exprs) ty -> do ty' <- trType ty
                                   trHead (Just ty') head =<< mapM trExpr exprs
  A.As e _ -> trExpr e

  A.App head exprs           -> trHead Nothing head =<< mapM trExpr exprs

  A.Match expr cases  -> do e <- trExpr expr
                            cases' <- sort <$> mapM (trCase (exprType e)) cases
                            return (T.Match e cases')
  A.Let letdecls expr -> trLetDecls letdecls expr
  A.Binder binder bindings expr -> newScope $ trBinder binder <$> mapM trLocalBinding bindings <*> trExpr expr
  A.Lit l -> return (literal (trLit l))

trLit :: A.Lit -> T.Lit
trLit (A.LitInt n) = T.Int n
trLit (A.LitNegInt n) = T.Int (negate n)
trLit A.LitTrue = T.Bool True
trLit A.LitFalse = T.Bool False

trHead :: Maybe (T.Type Id) -> A.Head -> [T.Expr Id] -> CM (T.Expr Id)
trHead mgt A.IfThenElse  [c,t,f] = return (makeIf c t f)
trHead mgt A.IfThenElse  args    = throwError $ "if-then-else with " <+> int (length args) <+> " arguments!"
trHead mgt (A.Const sym) args    =
  do x <- lkSym sym
     mt <- gets (fmap globalType . lookupGlobal x)
     case mt of
       Just pt
         | Just gbl <- makeGlobal x pt (map exprType args) mgt
         -> return (Gbl gbl :@: args)
         | otherwise
         -> throwError $ "Not a well-applied global:" <+> ppSym sym
                      $$ " with goal type " <+> case mgt of Nothing -> "Nothing"; Just t -> pp t
                      $$ " with argument types " <+> fsep (punctuate "," (map (pp . exprType) args))
                      $$ " with polymorphic type " <+> pp pt
       _ -> throwError $ "No type information for:" <+> ppSym sym

trHead _ x args = return (Builtin b :@: args)
 where
  b = case x of
    A.At       -> T.At
    A.And      -> T.And
    A.Or       -> T.Or
    A.Not      -> T.Not
    A.Implies  -> T.Implies
    A.Equal    -> T.Equal
    A.Distinct -> T.Distinct
    A.NumAdd   -> T.NumAdd
    A.NumSub   -> T.NumSub
    A.NumMul   -> T.NumMul
    A.NumDiv   -> T.NumDiv
    A.IntDiv   -> T.IntDiv
    A.IntMod   -> T.IntMod
    A.NumGt    -> T.NumGt
    A.NumGe    -> T.NumGe
    A.NumLt    -> T.NumLt
    A.NumLe    -> T.NumLe
    A.NumWiden -> T.NumWiden


trBinder :: A.Binder -> [Local Id] -> T.Expr Id -> T.Expr Id
trBinder b = case b of
  A.Lambda -> T.Lam
  A.Forall -> mkQuant T.Forall
  A.Exists -> mkQuant T.Exists

trCase :: T.Type Id -> A.Case -> CM (T.Case Id)
trCase goal_type (A.Case pattern expr) =
  newScope $ T.Case <$> trPattern goal_type pattern <*> trExpr expr

trPattern :: T.Type Id -> A.Pattern -> CM (T.Pattern Id)
trPattern goal_type p = case p of
  A.Default          -> return T.Default
  A.SimplePat sym    -> trPattern goal_type (A.ConPat sym [])
  A.ConPat sym bound ->
    do x <- lkSym sym
       mt <- gets (fmap globalType . lookupGlobal x)
       case mt of
         Just pt@(PolyType tvs arg res)
           | Just ty_app <- matchTypesIn tvs [(res,goal_type)] ->
             do let (var_types, _) = applyPolyType pt ty_app
                ls <- sequence
                   [ do b <- addSym LocalId b_sym
                        let l = Local b t
                        newLocal l
                        return l
                   | (b_sym,t) <- bound `zip` var_types
                   ]
                return (T.ConPat (Global x pt ty_app) ls)
         _ -> throwError $ "type-incorrect case"
  A.LitPat l -> return (T.LitPat (trLit l))

trType :: A.Type -> CM (T.Type Id)
trType t0 = case t0 of
  A.TyVar s -> do x <- lkSym s
                  mtv <- gets (isTyVar x)
                  if mtv then return (T.TyVar x)
                         else trType (A.TyApp s [])
  A.TyApp s ts -> T.TyCon <$> lkSym s <*> mapM trType ts
  A.ArrowTy ts -> (:=>:) <$> mapM trType (init ts) <*> trType (last ts)
  A.IntTy      -> return intType
  A.RealTy     -> return realType
  A.BoolTy     -> return boolType

