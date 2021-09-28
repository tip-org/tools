{-# LANGUAGE OverloadedStrings #-}
module Tip.Parser.Convert where

import Prelude hiding ((<>))
import Tip.Parser.AbsTIP as A -- from A ...
import Tip.Core          as T -- ... to T
import Tip.Pretty
import Tip.Pretty.SMT()

import Text.PrettyPrint
import Control.Monad.State
import Control.Monad.Except

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
runCM m = either (Left . show) Right $ runFreshFrom 0 (evalStateT (runScopeT m) M.empty)

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

symPos :: Symbol -> (Int, Int)
symPos (Unquoted (UnquotedSymbol (p, _))) = p
symPos (Quoted (QuotedSymbol (p, _))) = p

symStr :: Symbol -> String
symStr (Unquoted (UnquotedSymbol (_, s))) = s
symStr (Quoted (QuotedSymbol (_, s))) =
  unescape $ tail $ init s
  where
    unescape ('\\':x:xs) = x:unescape xs
    unescape (x:xs) = x:unescape xs
    unescape [] = []

ppSym :: Symbol -> Doc
ppSym sym = text (symStr sym) <+> "(" <> int x <> ":" <> int y <> ")"
  where
    (x, y) = symPos sym

lkSym :: Symbol -> CM Id
lkSym sym =
  do mik <- lift $ gets (M.lookup (symStr sym))
     case mik of
       Just (i,_) -> return $ i { idPos = Just (symPos sym) }
       Nothing    -> throwError $ "Symbol" <+> ppSym sym <+> "not bound"

addSym :: IdKind -> Symbol -> CM Id
addSym ik sym =
  do mik <- lift $ gets (M.lookup (symStr sym))
     case mik of
       Just (_,GlobalId)       -> throwError $ "Symbol" <+> ppSym sym <+> "is already globally bound"
       Just _ | ik == GlobalId -> throwError $ "Symbol" <+> ppSym sym <+> "is locally bound, and cannot be overwritten by a global"
       _                       -> return ()
     u <- lift (lift fresh)
     let i = Id (symStr sym) u (Just (symPos sym))
     lift $ modify (M.insert (symStr sym) (i,ik))
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
      DeclareDatatype name datatype ->
        let (Par tvs, _) = unpackData datatype in
        trDecl (DeclareDatatypes [DatatypeName name (fromIntegral (length tvs))] [datatype])
      DeclareDatatypes names datatypes ->
        do -- add their types, abstractly
           unless (length names == length datatypes) $
             throwError "declare-datatypes used with different number of names and definitions"
           forM_ (zip names datatypes) $ \(DatatypeName (AttrSymbol name attrs) arity, dt0) -> do
             let (Par tvs, _) = unpackData dt0
             unless (arity == fromIntegral (length tvs)) $
               throwError "declare-datatypes: arity declaration does not match number of type variables"
             sym <- addSym GlobalId name
             newScope $ do
               tvi <- mapM (addSym LocalId) tvs
               newSort (Sort sym (trAttrs attrs) tvi)
           ds <- forM (zip names datatypes) $ \(DatatypeName name _, dt0) ->
             newScope $ do
               let (Par tvs, dt) = unpackData dt0
               tvi <- mapM (addSym LocalId) tvs
               mapM newTyVar tvi
               trDatatype tvi name dt
           return emptyTheory{ thy_datatypes = ds }

      DeclareSort (AttrSymbol s attrs) n ->
        do i <- addSym GlobalId s
           tvs <- lift . lift $ mapM refresh (replicate (fromInteger n) i)
           return emptyTheory{ thy_sorts = [Sort i (trAttrs attrs) tvs] }

      DeclareConst sym (ConstTypeMono ty) ->
        trDecl (DeclareFun sym (FunTypeMono (InnerFunType [] ty)))
      DeclareConst sym (ConstTypePoly par ty) ->
        trDecl (DeclareFun sym (FunTypePoly par (InnerFunType [] ty)))

      DeclareFun sym (FunTypeMono ty) ->
        trDecl (DeclareFun sym (FunTypePoly emptyPar ty))
      DeclareFun sym (FunTypePoly par (InnerFunType args ty)) ->
        do d <- trFunDecl sym par args ty
           return emptyTheory{ thy_sigs = [d] }

      DefineFun (FunDecMono sym ty) body ->
        trDecl (DefineFun (FunDecPoly sym emptyPar ty) body)
      DefineFun dec@(FunDecPoly (AttrSymbol f _) _ _) body ->
        do thy <- trDecl (DefineFunRec dec body)
           let [fn] = thy_funcs thy
           when (func_name fn `elem` uses fn)
                (throwError $ ppSym f <+> "is recursive, but define-fun-rec was not used!")
           return thy

      DefineFunRec (FunDecMono sym ty) body ->
        trDecl (DefineFunRec (FunDecPoly sym emptyPar ty) body)
      DefineFunRec (FunDecPoly sym par (InnerFunDec binds ty)) body ->
        do sig <- trFunDecl sym par (map bindingType binds) ty
           withTheory emptyTheory{ thy_sigs = [sig] } $ do
             fn <- trFunDef sym par binds ty body
             return emptyTheory{ thy_funcs = [fn] }

      DefineFunsRec decs bodies ->
        do -- add their correct types, abstractly
           unless (length decs == length bodies) $
             throwError "define-funs-rec used with different number of signatures and bodies"
           fds <- sequence [trFunDecl sym tvs (map bindingType binds) ty | (sym, tvs, binds, ty) <- map unpackFunDec decs]
           withTheory emptyTheory{ thy_sigs = fds } $ do
             fns <- sequence
                [ trFunDef sym par binds ty body
                | (dec,body) <- decs `zip` bodies,
                  let (sym, par, binds, ty) = unpackFunDec dec
                ]
             return emptyTheory{ thy_funcs = fns }

      A.Formula role attrs expr -> trDecl (FormulaPar role attrs emptyPar expr)
      FormulaPar role attrs (Par tvs) expr ->
        do tvi <- mapM (addSym LocalId) tvs
           mapM newTyVar tvi
           let toRole A.Assert = T.Assert
               toRole A.Prove = T.Prove
           fm <- T.Formula (toRole role) (trAttrs attrs) tvi <$> trExpr expr
           return emptyTheory{ thy_asserts = [fm] }

emptyPar :: Par
emptyPar = Par []

unpackFunDec :: BracketedFunDec -> (AttrSymbol, Par, [Binding], A.Type)
unpackFunDec (BracketedFunDec (FunDecMono sym (InnerFunDec binds ty))) =
  (sym, emptyPar, binds, ty)
unpackFunDec (BracketedFunDec (FunDecPoly sym par (InnerFunDec binds ty))) =
  (sym, par, binds, ty)

trFunDecl :: AttrSymbol -> Par -> [A.Type] -> A.Type -> CM (T.Signature Id)
trFunDecl (AttrSymbol fsym attrs) (Par tvs) args res =
    newScope $
      do f <- addSym GlobalId fsym
         tvi <- mapM (addSym LocalId) tvs
         mapM newTyVar tvi
         pt <- PolyType tvi <$> mapM trType args <*> trType res
         return (Signature f (trAttrs attrs) pt)

trFunDef :: AttrSymbol -> Par -> [Binding] -> A.Type -> A.Expr -> CM (T.Function Id)
trFunDef (AttrSymbol fsym attrs) (Par tvs) bindings res_type body =
  newScope $
    do f <- lkSym fsym
       tvi <- mapM (addSym LocalId) tvs
       mapM newTyVar tvi
       args <- mapM trLocalBinding bindings
       Function f (trAttrs attrs) tvi args <$> trType res_type <*> trExpr body

unpackData :: A.Datatype -> (Par, A.InnerDatatype)
unpackData (DatatypeMono dt) = (emptyPar, dt)
unpackData (DatatypePoly par dt) = (par, dt)

trDatatype :: [Id] -> AttrSymbol -> A.InnerDatatype -> CM (T.Datatype Id)
trDatatype tvs (AttrSymbol sym attrs) (A.InnerDatatype constructors) =
  do x <- lkSym sym
     T.Datatype x (trAttrs attrs) tvs <$> mapM trConstructor constructors

trConstructor :: A.Constructor -> CM (T.Constructor Id)
trConstructor (A.Constructor (AttrSymbol name attrs) args) =
  do c <- addSym GlobalId name
     is_c <- addSym GlobalId (Unquoted (UnquotedSymbol (symPos name, "is-" ++ symStr name)))
     T.Constructor c (trAttrs attrs) is_c <$> mapM (trBinding GlobalId) args

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

polySym :: A.PolySymbol -> A.Symbol
polySym (A.As x _) = x
polySym (A.NoAs x) = x

polyTys :: A.PolySymbol -> CM (Maybe [T.Type Id])
polyTys (A.As _ tys) = Just <$> mapM trType tys
polyTys (A.NoAs _) = return Nothing

trExpr :: A.Expr -> CM (T.Expr Id)
trExpr e0 = case e0 of
  A.Var sym ->
    do x <- lkSym (polySym sym)
       ml <- gets (lookupLocal x)
       case ml of
         Just t -> do
           tys <- polyTys sym
           case tys of
             Just (_:_) ->
               throwError $ "Local variable" <+> ppSym (polySym sym) <+> "should not be given type arguments"
             _ ->
               return (Lcl (Local x t))
         _      -> trExpr (A.App (A.Const sym) [])

  A.App head exprs           -> trHead head =<< mapM trExpr exprs

  A.Match expr cases  -> do e <- trExpr expr
                            cases' <- mapM (trCase (exprType e)) cases
                            return (T.caseExpr e cases')
  A.Let letdecls expr -> trLetDecls letdecls expr
  A.Binder binder bindings expr -> newScope $ trBinder binder <$> mapM trLocalBinding bindings <*> trExpr expr
  A.Lit l -> return (literal (trLit l))

trLit :: A.Lit -> T.Lit
trLit (A.LitInt n) = T.Int n
trLit (A.LitNegInt n) = T.Int (negate n)
trLit A.LitTrue = T.Bool True
trLit A.LitFalse = T.Bool False

trHead :: A.Head -> [T.Expr Id] -> CM (T.Expr Id)
trHead A.IfThenElse  [c,t,f] = return (makeIf c t f)
trHead A.IfThenElse  args    = throwError $ "if-then-else with " <+> int (length args) <+> " arguments!"
trHead (A.Const sym) args    =
  do x <- lkSym (polySym sym)
     mtys <- polyTys sym
     mt <- gets (fmap globalType . lookupGlobal x)
     case mt of
       Nothing -> throwError $ "No type information for:" <+> ppSym (polySym sym)
       Just pt ->
         case mtys of
           Just tys ->
             if length tys == length (polytype_tvs pt) then
               return (Gbl (Global x pt tys) :@: args)
             else
               throwError $
                 "Global applied to wrong number of type arguments:" <+> ppSym (polySym sym) $$
                 " expected" <+> pp (length (polytype_tvs pt)) <> ":" <+> sep (punctuate comma (map ppVar (polytype_tvs pt))) $$
                 " but got" <+> pp (length tys) <> ":" <+> sep (punctuate comma (map pp tys))
           Nothing ->
             case makeGlobal x pt (map exprType args) Nothing of
               Just gbl -> return (Gbl gbl :@: args)
               Nothing ->
                 throwError $ "Not a well-applied global:" <+> ppSym (polySym sym)
                   $$ " with argument types " <+> fsep (punctuate "," (map (pp . exprType) args))
                   $$ " with polymorphic type " <+> pp pt

trHead A.At       args = return (Builtin T.At       :@: args)
trHead A.And      args = return (Builtin T.And      :@: args)
trHead A.Or       args = return (Builtin T.Or       :@: args)
trHead A.Not      args = return (Builtin T.Not      :@: args)
trHead A.Implies  args = return (Builtin T.Implies  :@: args)
trHead A.Equal    args = return (Builtin T.Equal    :@: args)
trHead A.Distinct args = return (Builtin T.Distinct :@: args)
trHead A.NumAdd   args = return (Builtin T.NumAdd   :@: args)
trHead A.NumSub   args = return (Builtin T.NumSub   :@: args)
trHead A.NumMul   args = return (Builtin T.NumMul   :@: args)
trHead A.NumDiv   args = return (Builtin T.NumDiv   :@: args)
trHead A.IntDiv   args = return (Builtin T.IntDiv   :@: args)
trHead A.IntMod   args = return (Builtin T.IntMod   :@: args)
trHead A.NumGt    args = return (Builtin T.NumGt    :@: args)
trHead A.NumGe    args = return (Builtin T.NumGe    :@: args)
trHead A.NumLt    args = return (Builtin T.NumLt    :@: args)
trHead A.NumLe    args = return (Builtin T.NumLe    :@: args)
trHead A.NumWiden args = return (Builtin T.NumWiden :@: args)

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

trAttrs :: [A.Attr] -> [T.Attribute]
trAttrs = nubBy ((==) `on` fst) . map trAttr

trAttr :: A.Attr -> T.Attribute
trAttr (NoValue (Keyword (':':name))) = (name, Nothing)
trAttr (Value (Keyword (':':name)) value) = (name, Just (symStr value))
trAttr _ = error "lexical error in keyword"
