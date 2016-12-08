{-# LANGUAGE RecordWildCards, CPP, ScopedTypeVariables #-}
module Tip.GHC where

#include "errors.h"
import CoreSyn
import GHC hiding (Id, exprType, DataDecl, Name, typeKind)
import qualified GHC
import Tip.Fresh
import Var hiding (Id)
import qualified Var
import Tip.GHC.Annotations hiding (Lit, Cast)
import qualified Tip.GHC.Annotations as Tip
import Outputable
import Tip.Pretty
import Name hiding (Name, varName)
import Data.List
import Tip.Pretty.SMT hiding (apply)
import TysPrim
import TysWiredIn
import MkCore
import PrelNames
import Constants
import BasicTypes hiding (Inline)
import Control.Monad.Trans.Writer
import Data.Char
import Avail
import Tip.Utils hiding (Rec, NonRec)
import Data.Generics.Geniplate
import Literal
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Tip.Core as Tip
import Tip.Core hiding (Type, Case, Let, Lam, Lit, exprType)
import ConLike
import Annotations
import Tip.GHC.Params
import GHC.Paths
import HscTypes
import TyCon
import DataCon
import Type
import GHC.Serialized
import Id hiding (Id)
import System.Exit
import Control.Monad.IO.Class
import Control.Monad
import UniqFM
import DynFlags
import Data.IORef
import Kind
import CoreUtils
import qualified Data.ByteString.Char8 as BS
import Tip.Passes
import Control.Exception
import Data.Typeable(Typeable)
import qualified Text.PrettyPrint as PP
import Control.DeepSeq
import Tip.Lint
import Module
import Data.List.Split
import Control.Monad.Trans.State.Strict

----------------------------------------------------------------------
-- The main program.
----------------------------------------------------------------------

-- Translate a Haskell file into a TIP theory.
readHaskellFile :: Params -> String -> IO (Theory Id)
readHaskellFile params@Params{..} name =
  runGhc (Just libdir) $ do
    -- Set the GHC flags.
    dflags <- getSessionDynFlags
    (dflags, _, _) <-
      parseDynamicFlagsCmdLine dflags $ map noLoc $
        param_include ++
        words ("-hide-package base -hide-package tip-ghc -package tip-prelude " ++
               "-O0 -fexpose-all-unfoldings -fno-ignore-interface-pragmas " ++
               "-fno-omit-interface-pragmas -funfolding-creation-threshold=0 -funfolding-use-threshold=0")
    -- Don't generate object code.
    setSessionDynFlags dflags {
      hscTarget = HscInterpreted,
      ghcLink = LinkInMemory,
      ghcMode = CompManager }

    -- Compile everything.
    target <- guessTarget name Nothing
    setTargets [target]
    ok <- load LoadAllTargets

    -- Make sure all the built-in TIP stuff gets loaded.
    findModule (mkModuleName "Prelude") Nothing >>= getModuleInfo
    findModule (mkModuleName "Prelude.Prim") Nothing >>= getModuleInfo
    findModule (mkModuleName "Tip") Nothing >>= getModuleInfo

    -- Finally, extract the TIP code from the compiled modules.
    if succeeded ok then do
      -- GHC distinguishes modules in the current package ("home"
      -- modules) from external modules. The way you access them is
      -- totally different. However, they both live in the HscEnv.
      HscEnv{..} <- getSession

      -- Home modules live in the "home package table", which contains
      -- one ModDetails record per module.
      let
        home = mconcat
          [ program (eltsUFM md_types) (mkAnnEnv md_anns)
          | HomeModInfo{hm_details = ModDetails{..}} <- eltsUFM hsc_HPT ]

      -- Away modules are combined into one giant record, the "external
      -- package state".
      EPS{..} <- liftIO $ readIORef hsc_EPS
      let away = program (eltsUFM eps_PTE) eps_ann_env

          mods =
            [(hm_iface mod, Home) | mod <- eltsUFM hsc_HPT] ++
            [(mod, Away) | mod <- moduleEnvElts eps_PIT]

      -- Finally, a few types (such as lists) are defined in GHC itself
      -- rather than a package. We have to add those by hand.
      Just (AnId fromIntegerId) <- lookupName fromIntegerName
      Just (AnId fromRationalId) <- lookupName fromRationalName
      Just (ATyCon integerTyCon) <- lookupName integerTyConName
      Just (ATyCon ratioTyCon) <- lookupName ratioTyConName
      Just (AConLike (RealDataCon ratioDataCon)) <-
        lookupGlobalName ratioDataConName
      Just (AnId eqId) <- lookupName eqName
      let builtin =
            Program (Map.fromList builtinTypes)
              (Map.fromList builtinGlobals)
          builtinTypes =
            [tyCon listTyCon [Name "list"],
             tyCon boolTyCon [PrimType Boolean],
             tyCon integerTyCon [PrimType Integer],
             tyCon ratioTyCon [PrimType Real]] ++
            [tyCon (tupleTyCon Boxed i) [Name (tupleName i)]
            | i <- [0..mAX_TUPLE_SIZE]]
          builtinGlobals =
            [specialFun pAT_ERROR_ID Error,
             specialFun fromIntegerId Tip.Cast,
             specialFun fromRationalId Tip.Cast,
             specialFun eqId (Primitive Equal 2),
             dataCon ratioDataCon [SomeSpecial Rational],
             dataCon consDataCon  [Name "cons", Projections ["head", "tail"]],
             dataCon nilDataCon   [Name "nil"],
             dataCon falseDataCon [Literal (Bool False)],
             dataCon trueDataCon  [Literal (Bool True)]] ++
            [dataCon (tupleDataCon Boxed i) [Name (tupleName i)]
            | i <- [0..mAX_TUPLE_SIZE]]
          tupleName 0 = "unit"
          tupleName 2 = "pair"
          tupleName _ = "tuple"
          specialFun x spec = (x, FunInfo (Var x) [SomeSpecial spec])

      -- Put builtin before away so that it takes precedence
      let prog = mconcat [home, builtin, away]

      when (PrintCore `elem` param_debug_flags) $
        liftIO $ putStrLn (showOutputable home)

      when (PrintAllCore `elem` param_debug_flags) $
        liftIO $ putStrLn (showOutputable prog)

      -- Work out an initial set of functions and properties.
      let keep = filter (isIncluded param_keep mods) (Map.keys (prog_globals prog))
          (props, funcs) = partition (isPropType prog . varType) keep

      let
        thy =
          completeTheory prog $ declsToTheory $
          [ AssertDecl (tipFormula prog prop (global_definition (globalInfo prog prop)))
          | prop <- props ] ++
          [ FuncDecl (tipFunction prog func (global_definition (globalInfo prog func)))
          | func <- funcs ]

      when (PrintInitialTheory `elem` param_debug_flags) $
        liftIO $ putStrLn (ppRender thy)

      return $ lint "conversion to TIP" $ clean $ freshPass (simplifyTheory gently >=> eliminateLetRec) thy
    else liftIO $ exitWith (ExitFailure 1)

-- Did the user ask us to include this function or property?
data Source = Home | Away deriving (Eq, Show)
isIncluded :: Maybe [String] -> [(ModIface, Source)] -> Var -> Bool
isIncluded names mods x =
  case filter (foundIn . fst) mods of
    [] -> False
    ((mod, source):_) ->
      case names of
        Nothing -> source == Home
        Just names ->
          (modPrefix mod source, getOccString x) `elem` map parseModulePrefix names
  where
    foundIn mod =
      varName x `elem` [ y | Avail _ y <- mi_exports mod ]

    modPrefix _ Home = ""
    modPrefix mod Away = moduleNameString (moduleName (mi_module mod))

-- Split a function name up into the module part and the function part.
parseModulePrefix :: String -> (String, String)
parseModulePrefix str = (intercalate "." mods, intercalate "." funcs)
  where
    components = splitOn "." str
    (mods, funcs) = span isModule components
    isModule (x:_) = isUpper x
    isModule _ = False

-- Is this type a reasonable type for a property?
isPropType :: Program -> GHC.Type -> Bool
isPropType prog = prop . expandTypeSynonyms
  where
    prop ty
      | Just (_, res) <- splitFunTy_maybe ty = prop res
      | Just (_, res) <- splitForAllTy_maybe ty = prop res
      | Just (tc, []) <- splitTyConApp_maybe ty,
        PropType `elem` typeAnnotations prog tc = True
      | otherwise = False

----------------------------------------------------------------------
-- A type representing the Haskell program
-- that's friendlier than what we get from GHC.
----------------------------------------------------------------------

-- The program, a set of data types and functions.
data Program =
  Program {
    -- Data types.
    prog_types     :: Map TyCon TypeInfo,
    -- Constructors and functions.
    prog_globals   :: Map Var GlobalInfo }

data TypeInfo =
  TypeInfo {
    -- The type variables which will be used in the Datatype.
    type_tvs          :: [TyVar],
    -- The datatype's constructors.
    type_constructors :: [Var],
    -- Any annotations.
    type_annotations  :: [TipAnnotation] }

data GlobalInfo =
  ConInfo {
    -- The type arguments taken by the constructor.
    global_tvs         :: [TyVar],
    -- The arguments taken by the constructor.
    global_args        :: [Type],
    -- The constructor's return type.
    -- Should be a type constructor applied to some type variables.
    global_res         :: Type,
    -- The type constructor.
    -- Should match the one in global_res.
    global_tycon       :: TyCon,
    -- Any annotations.
    global_annotations :: [TipAnnotation] } |
  FunInfo {
    -- The function's definition (typically a lambda-expression).
    global_definition  :: CoreExpr,
    -- Any annotations.
    global_annotations :: [TipAnnotation] }

instance Monoid Program where
  mempty = Program mempty mempty
  p1 `mappend` p2 =
    Program
      (prog_types p1 `mappend` prog_types p2)
      (prog_globals p1 `mappend` prog_globals p2)

-- Look up the TypeInfo for a type constructor.
typeInfo :: Program -> TyCon -> TypeInfo
typeInfo prog ty = Map.findWithDefault err ty (prog_types prog)
  where
    err = ERROR("Type " ++ showOutputable ty ++ " not found or not supported")

-- Look up the GlobalInfo for a constructor or global function.
globalInfo :: Program -> Var -> GlobalInfo
globalInfo prog global = Map.findWithDefault err global (prog_globals prog)
  where
    err = ERROR("Global " ++ showOutputable global ++ " not found or not supported")

-- Look up the annotations for a type constructor.
typeAnnotations :: Program -> TyCon -> [TipAnnotation]
typeAnnotations prog ty =
  case Map.lookup ty (prog_types prog) of
    Nothing -> []
    Just ti -> type_annotations ti

-- Look up the annotations for a global.
globalAnnotations :: Program -> Var -> [TipAnnotation]
globalAnnotations prog global =
  case Map.lookup global (prog_globals prog) of
    Nothing -> []
    Just gi -> global_annotations gi

-- Build a program from a list of declarations and a list of annotations.
program :: [TyThing] -> AnnEnv -> Program
program things anns = Program types globals
  where
    types =
      Map.fromList
      [ tyCon tc (annotations (tyConName tc))
      | ATyCon tc <- things,
        isAlgTyCon tc ]
    globals =
      Map.fromList $
      [ dataCon dc (annotations (dataConName dc))
      | AConLike (RealDataCon dc) <- things ] ++
      [ (id, FunInfo unfolding (annotations (idName id)))
      | AnId id <- things,
        Just unfolding <- [maybeUnfoldingTemplate (realIdUnfolding id)] ]
    
    annotations :: GHC.Name -> [TipAnnotation]
    annotations name =
      findAnns deserializeWithData anns (NamedTarget name)

-- Find the information for a type constructor.
tyCon :: TyCon -> [TipAnnotation] -> (TyCon, TypeInfo)
tyCon tc anns =
  (tc, TypeInfo tvs (map dataConWorkId dcs) anns)
  where
    tvs = tyConTyVars tc
    dcs = tyConDataCons tc

-- Find the information for a data constructor.
dataCon :: DataCon -> [TipAnnotation] -> (Var, GlobalInfo)
dataCon dc anns =
  (dataConWorkId dc,
   ConInfo
     (dataConUnivTyVars dc)
     (dataConRepArgTys dc)
     (dataConOrigResTy dc)
     (dataConTyCon dc) anns)

----------------------------------------------------------------------
-- The type of identifiers in our output theory.
----------------------------------------------------------------------

data Id =
    TypeId   String TyCon
  | GlobalId String Var
  | LocalId  String Int
  | TyVarId  TyVar
  | ProjectionId String Var Int
  | DiscriminatorId String Var
  | ErrorId
  | CastId
  deriving (Eq, Ord)

instance NFData Id where
  rnf x = x `seq` ()

instance PrettyVar Id where
  varStr (TypeId x _)   = x
  varStr (GlobalId x _) = x
  varStr (LocalId x _)  = x
  varStr (TyVarId x)
    | isSystemName (Var.varName x) = "a"
    | otherwise = getOccString x
  varStr (ProjectionId x _ _) = x
  varStr (DiscriminatorId x _) = x
  varStr ErrorId = "error"
  varStr CastId = "cast"

instance Show Id where
  show = varStr

instance Name Id where
  fresh = freshNamed "x"
  freshNamed x = fmap (LocalId x) fresh

  refreshNamed s n
    | "aux" `isPrefixOf` varStr n = freshNamed s
    | otherwise = freshNamed (s ++ "-" ++ varStr n)
  getUnique (LocalId _ n) = n
  getUnique _ = 0

-- Make a string describing a global.
globalStr :: Program -> Var -> String
globalStr prog x =
  case [ y | Name y <- globalAnnotations prog x ] of
    (y:_) -> y
    [] | isSystemName (Var.varName x) -> "x"
       | otherwise -> getOccString x

-- Construct an Id from a global.
globalId :: Program -> Var -> Id
globalId prog x = GlobalId (globalStr prog x) x

-- Construct an Id from a type constructor.
typeId :: Program -> TyCon -> Id
typeId prog x = TypeId name x
  where
    name =
      case [ y | Name y <- typeAnnotations prog x ] of
        (y:_) -> y
        [] -> getOccString x

-- Construct an Id from a constructor projection.
projectionId :: Program -> Var -> Int -> Id
projectionId prog x n =
  case [ xs | Projections xs <- globalAnnotations prog x ] of
    (xs:_)
      | length xs < n ->
        ERROR("Constructor " ++ showOutputable x ++ " should have at least " ++
              show n ++ " projections, but has only " ++
              show (length xs) ++ ": " ++ intercalate ", " xs)
      | otherwise -> ProjectionId (xs !! (n-1)) x n
    _ -> ProjectionId ("proj" ++ show n ++ "-" ++ globalStr prog x) x n

-- Construct an Id from a constructor discriminator.
discriminatorId :: Program -> Var -> Id
discriminatorId prog x =
  DiscriminatorId ("is-" ++ globalStr prog x) x

----------------------------------------------------------------------
-- The main translation functions. 
--
-- We translate Haskell datatypes into TIP datatypes, and Haskell
-- functions into TIP lambda-functions. (That is, all our globals
-- have an arity of 0.)
--
-- The following types are translated specially:
--   * Types annotated with Primitive turn into TIP builtins.
--     (Currently these are Bool, Prop, Int and Float.)
--   * Any becomes an uninterpreted sort.
--     (Any occurs when a polymorphic function is applied at a completely
--     unconstrained type.)
--   * Typeclass dictionaries and Void# are erased from function arguments.
--
-- The following functions are translated specially:
--   * Prelude.primitive becomes a TIP builtin.
--   * fromInteger n and fromRational (m :% n) become numeric literals.
--   * True and False turn into TIP booleans.
--   * patError turns into a fictitious local variable ErrorId.
--     We later eliminate ErrorId as part of cleaning up the theory.
----------------------------------------------------------------------

-- Take a theory which may be missing some function and datatype
-- definitions, and pull those definitions in from the Haskell program.
completeTheory :: Program -> Theory Id -> Theory Id
completeTheory prog thy =
  inContext (show msg) $
    if null funcs && null types then thy else
    completeTheory prog $!!
      thy `mappend`
      declsToTheory (map makeFunc funcs ++ map makeType types)
  where
    funcs :: [Var]
    funcs =
      usort
      [ x
      | name@(GlobalId _ x) <- map gbl_name (usort (universeBi thy)),
        FunInfo{} <- [globalInfo prog x],
        name `notElem` map func_name (thy_funcs thy),
        name `notElem` map sig_name (thy_sigs thy) ]
    
    types :: [TyCon]
    types =
      usort
      [ x | TyCon name@(TypeId _ x) _ <- usort (universeBi thy),
        name `notElem` map sort_name (thy_sorts thy),
        name `notElem` map data_name (thy_datatypes thy) ]

    makeFunc :: Var -> Decl Id
    makeFunc x =
      FuncDecl (tipFunction prog x (global_definition (globalInfo prog x)))

    makeType :: TyCon -> Decl Id
    makeType ty
      | isAny ty = SortDecl (Sort (typeId prog ty) [])
      | otherwise = DataDecl (tipDatatype prog ty)

    msg =
      PP.vcat [
        PP.text "While elaborating the theory:",
        PP.nest 2 (pp thy) ]

-- Translate a Haskell datatype declaration to TIP.
tipDatatype :: Program -> TyCon -> Tip.Datatype Id
tipDatatype prog tc =
  Datatype {
    data_name = typeId prog tc,
    data_tvs  = map TyVarId type_tvs,
    data_cons = map (tipConstructor prog) type_constructors }
  where
    TypeInfo{..} = typeInfo prog tc

-- Translate a Haskell constructor declaration to TIP.
tipConstructor :: Program -> Var -> Tip.Constructor Id
tipConstructor prog x =
  Constructor {
    con_name    = globalId prog x,
    con_discrim = discriminatorId prog x,
    con_args    = zipWith con [1..] global_args }
  where
    ConInfo{..} = globalInfo prog x
    TypeInfo{..} = typeInfo prog global_tycon
    
    -- The type variables in the DataCon might not be the same as in
    -- the parent TyCon. Applying this substitution corrects that.
    Just sub = matchTypes [(tipType prog global_res, dataTy)]
    subst = uncurry applyType (unzip sub)
    dataTy = TyCon (typeId prog global_tycon) (map (TyVar . TyVarId) type_tvs)

    con i ty =
      (projectionId prog x i, subst (tipType prog ty))

-- Translate a Haskell polymorphic type to TIP.
tipPolyType :: Program -> GHC.Type -> Tip.PolyType Id
tipPolyType prog pty =
  PolyType {
    polytype_tvs  = map TyVarId tvs,
    polytype_args = [],
    polytype_res  = tipType prog ty
  }
  where
    (tvs, ty)   = splitForAllTys (expandTypeSynonyms pty)

-- Translate a Haskell type to TIP.
tipType :: Program -> GHC.Type -> Tip.Type Id
tipType prog = tipTy . expandTypeSynonyms
  where
    tipTy ty
      | Just tv <- getTyVar_maybe ty = TyVar (TyVarId tv)
      | Just (arg, res) <- splitFunTy_maybe ty = tipFunTy arg res
      | Just (tc, tys) <- splitTyConApp_maybe ty =
          tipTyCon tc (typeAnnotations prog tc) tys
      | otherwise =
        ERROR("Illegal monomorphic type in Haskell program: " ++
              showOutputable ty)

    tipTyCon tc anns _ | (ty:_) <- [ty | PrimType ty <- anns] =
      BuiltinType ty
    tipTyCon tc _ tys =
      TyCon (typeId prog tc) (map tipTy tys)

    tipFunTy arg res
      | eraseType arg = tipTy res
      | otherwise = [tipTy arg] :=>: tipTy res

-- Translate a Haskell property to TIP.
tipFormula :: Program -> Var -> CoreExpr -> Tip.Formula Id
tipFormula prog x t =
  Formula Prove UserAsserted func_tvs $
    freshPass quantify func_body
  where
    Function{..} = tipFunction prog x t

    -- Try to use names from the formula if possible
    quantify (Tip.Lam xs t) =
      Quant NoInfo Forall xs <$> quantify t
    quantify t =
      case Tip.exprType t of
        args :=>: res -> do
          xs <- mapM freshLocal args
          Quant NoInfo Forall xs <$>
            quantify (apply t (map Lcl xs))
        _ -> return t

-- The context which expressions get translated in.
data Context =
  Context {
    -- The variables which are in scope.
    ctx_vars  :: Map Var (Local Id),
    -- The let-bound functions which are in scope.
    ctx_funs  :: Map Var ([Tip.Type Id] -> Tip.Expr Id),
    -- The translated expression will be applied to these types.
    ctx_types :: [Tip.Type Id] }

-- Translate a Haskell function definition to TIP.
tipFunction :: Program -> Var -> CoreExpr -> Tip.Function Id
tipFunction prog x t =
  runFresh $ fun (Context Map.empty Map.empty []) x t
  where
    fun :: Context -> Var -> CoreExpr -> Fresh (Tip.Function Id)
    fun ctx x t = inContextM (showOutputable msg) $ do
      let pty@PolyType{..} = polyType x
      body <- expr ctx { ctx_types = map TyVar (polytype_tvs) } t
      return $
        Function {
          func_name = globalId prog x,
          func_tvs  = polytype_tvs,
          func_args = [],
          func_res  = polytype_res,
          func_body = body }
      where
        msg =
          vcat [
            text "While translating" <+> ppr x <+> text "::" <+> ppr (varType x) <+> text "with body:",
            nest 2 (ppr t) ]

    expr :: Context -> CoreExpr -> Fresh (Tip.Expr Id)
    expr ctx (Var inl `App` Type _ `App` e)
      | SomeSpecial InlineIt `elem` globalAnnotations prog inl =
        expr ctx (inline e)
    expr ctx e@(Var prim `App` Type ty `App` Lit (MachStr name))
      | Special `elem` globalAnnotations prog prim =
        case reads (BS.unpack name) of
          [(spec, "")] ->
            special ctx (tipType prog ty) spec
          _ -> ERROR("Unknown special " ++ BS.unpack name)
    expr ctx (Lit l) = return (literal (lit l))
    expr ctx e@(Var ratio `App` Type _ `App` Lit (LitInteger m _) `App` Lit (LitInteger n _))
      | SomeSpecial Rational `elem` globalAnnotations prog ratio =
        return $
          Builtin NumDiv :@:
            [Builtin NumWiden :@: [Builtin (Tip.Lit (Tip.Int m)) :@: []],
             Builtin NumWiden :@: [Builtin (Tip.Lit (Tip.Int n)) :@: []]]
    expr ctx (Var x) = var ctx x
    expr ctx (App t u) = app ctx t u
    expr ctx (Lam x e) = lam ctx x e
    expr ctx (Let (NonRec x t) u) = letNonRec ctx x t u
    expr ctx (Let (Rec binds) t) = letRec ctx binds t
    expr ctx (Case t x _ alts) = caseExp ctx (varType x) x t alts
    expr ctx (Tick _ e) = expr ctx e
    expr _ e = ERROR("Unsupported expression: " ++ showOutputable e)

    inline :: CoreExpr -> CoreExpr
    inline (Var x) =
      global_definition (globalInfo prog x)
    inline (App t u) =
      App (inline t) u
    inline t = t

    lit :: Literal -> Tip.Lit
    lit (LitInteger n _) = Int n
    lit l = ERROR("Unsupported literal: " ++ showOutputable l)

    special :: Context -> Tip.Type Id -> Special -> Fresh (Tip.Expr Id)
    special ctx ty (Primitive name arity) = do
      names <- replicateM arity fresh
      let
        funArgs (t :=>: u) = t ++ funArgs u
        funArgs _ = []

        args = zipWith Local names (funArgs ty)

      return $
        foldr (\arg e -> Tip.Lam [arg] e)
          (Builtin name :@: map Lcl args)
          args
    special ctx ([ty@([argTy] :=>: _)] :=>: _) (QuantSpecial quant) = do
      -- \p -> Quant quant (\x -> p x)
      pred <- freshLocal ty
      arg  <- freshLocal argTy
      return $
        Tip.Lam [pred] (Quant NoInfo quant [arg] (apply (Lcl pred) [Lcl arg]))
    special ctx ty Tip.Cast =
      return (Lcl (Local CastId ty))
    special _ ty Error = return (errorTerm ty)
    special _ ty spec =
      ERROR("Unsupported special " ++ show spec ++ " :: " ++ ppRender ty)

    var :: Context -> Var -> Fresh (Tip.Expr Id)
    var ctx x
      | Inline `elem` globalAnnotations prog x =
        expr ctx (inline (Var x))
    var ctx f
      | (spec:_) <-
        [spec | SomeSpecial spec <- globalAnnotations prog f] = do
          let ([], ty) = applyPolyType (polyType f) (ctx_types ctx)
          special ctx ty spec
    var ctx x
      | (l:_) <- [l | Literal l <- globalAnnotations prog x] =
          return (literal l)
    var ctx x
      | Just fun <- Map.lookup x (ctx_funs ctx) =
        return (fun (ctx_types ctx))
      | Just var <- Map.lookup x (ctx_vars ctx) =
        return (Lcl var)
      | otherwise = do
        case globalInfo prog x of
          ConInfo{..} -> do
            -- Work out the type of the constructor.
            let
              TyCon _ tys =
                applyType (map TyVarId global_tvs) (ctx_types ctx)
                  (tipType prog global_res)
              dt  = tipDatatype prog global_tycon
              con = tipConstructor prog x
              global = constructor dt con tys
            -- Curry the constructor.
            names <-
              replicateM (length global_args) fresh
            let args = zipWith Local names (fst (gblType global))
            return $
              foldr (\arg e -> Tip.Lam [arg] e)
                (Gbl global :@: map Lcl args)
                args
          FunInfo{} -> do
            let
              global =
                Global (globalId prog x) (polyType x) (ctx_types ctx)
            return (Gbl global :@: [])

    app :: Context -> CoreExpr -> CoreExpr -> Fresh (Tip.Expr Id)
    app ctx t (Type u) = do
      let ty = tipType prog u
      expr ctx { ctx_types = ty:ctx_types ctx } t
    app ctx t u
      | eraseType (exprType u) = expr ctx t
      | otherwise = do
          t <- expr ctx t
          u <- expr ctx u
          return (apply t [u])

    lam :: Context -> Var -> CoreExpr -> Fresh (Tip.Expr Id)
    lam ctx x e
      | eraseType (varType x) = expr ctx e
      | isTyVar x =
        case ctx_types ctx of
          [] -> ERROR("Expression not applied to enough type arguments")
          (ty:tys) -> do
            e' <- expr ctx { ctx_types = tys } e
            return (substTypes [TyVarId x] [ty] e')
      | otherwise =
        bindVar ctx x $ \ctx local ->
          Tip.Lam [local] <$> expr ctx e

    letNonRec :: Context -> Var -> CoreExpr -> CoreExpr -> Fresh (Tip.Expr Id)
    letNonRec ctx x t u = do
      -- If x is polymorphic, we inline it. This is because
      -- non-recursive TIP let-bindings are monomorphic.
      --
      -- We could instead solve this by translating polymorphic let to
      -- letrec. But this doesn't quite work, because GHC sometimes
      -- generates the following type of code for pattern-match failures:
      --    let fail :: Void# -> a
      --        fail = patError "pattern match failed"
      --    in case xs of { [] -> ...; (y:ys) -> fail void# }
      -- If we translate this to a letrec, the fail function will get
      -- lifted to the top level. It will then get compiled into an
      -- uninterpreted function and the case-expression becomes:
      --    case xs of { [] -> ...; (y:ys) -> fail }
      -- What we would like to get, however, is:
      --    case xs of { [] -> ... }
      -- These two expressions are not the same. The value of both
      -- expressions is unspecified when xs is a cons. However,
      -- the second expression can give different results for
      -- different values of xs, but the first one always gives the
      -- same result (namely whatever the value of fail is).
      --
      -- By inlining all polymorphic let-bindings, we avoid all this
      -- nonsense and hopefully translate partial pattern matching
      -- into partial TIP functions.
      f <- fun ctx x t
      case func_tvs f of
        [] ->
          bindVar ctx x $ \ctx name ->
            Tip.Let name (func_body f) <$>
            expr ctx u
        _ -> do
          let g tys = substTypes (func_tvs f) tys (func_body f)
          bindInlineFun ctx x g $ \ctx ->
            expr ctx u

    letRec :: Context -> [(Var, CoreExpr)] -> CoreExpr -> Fresh (Tip.Expr Id)
    letRec ctx binds t = do
      let vars   = map fst binds
          bodies = map snd binds

      -- Bring all the bindings into scope.
      bindMany bindFun ctx vars $ \ctx names -> do
        -- Translate all the bodies.
        fs <- sequence $
          [ do { f <- fun ctx var body; return f { func_name = name } }
          | (var, body, name) <- zip3 vars bodies names ]

        LetRec fs <$> expr ctx t

    caseExp :: Context -> Type -> Var -> CoreExpr -> [Alt Var] -> Fresh (Tip.Expr Id)
    -- TIP invariant: empty case statements are not allowed
    caseExp _ _ x _ [] = return (errorTerm (monoType x))
    caseExp ctx ty x t alts = do
      -- Get the parameters of the type constructor
      let TyCon _ tys = tipType prog ty
      -- We turn GHC's
      --   case t of x { .. ALTS .. }
      -- into
      --   let x = t in case x of { .. ALTS .. }
      t <- expr ctx t
      bindVar ctx x $ \ctx var ->
        Tip.Let var t <$> Tip.Match (Lcl var) <$>
        mapM (caseAlt ctx tys) alts

    caseAlt :: Context -> [Tip.Type Id] -> Alt Var -> Fresh (Tip.Case Id)
    caseAlt ctx _ (DEFAULT, [], e) =
      Tip.Case Default <$> expr ctx e
    caseAlt ctx _ (LitAlt l, [], e) =
      Tip.Case (Tip.LitPat (lit l)) <$> expr ctx e
    caseAlt ctx _ (DataAlt dc, [], e)
      | (x:_) <- [x | Literal x <- globalAnnotations prog (dataConWorkId dc)] =
        Tip.Case (Tip.LitPat x) <$> expr ctx e
    caseAlt ctx tys (DataAlt dc, args, e) = do
      -- Make the constructor.
      let conId = dataConWorkId dc
          ConInfo{..} = globalInfo prog conId
          con = tipConstructor prog conId
          datatype = tipDatatype prog global_tycon
          global = constructor datatype con tys
      
      -- Make variables for the arguments of the constructor.
      bindMany bindVar ctx args $ \ctx locals ->
        Tip.Case (ConPat global locals) <$> expr ctx e

    -- A term which represents a runtime error.
    errorTerm :: Tip.Type Id -> Tip.Expr Id
    errorTerm ty = Lcl (Local ErrorId ty)

    -- Get the TIP type of a variable.
    monoType :: Var -> Tip.Type Id
    monoType = tipType prog . varType
    polyType :: Var -> Tip.PolyType Id
    polyType = tipPolyType prog . varType
      
    -- Bring a new variable into scope.
    bindVar :: Context -> Var -> (Context -> Local Id -> Fresh a) -> Fresh a
    bindVar ctx x k = do
      name <- freshNamed (globalStr prog x)
      let var = Local name (monoType x)
      k ctx { ctx_vars = Map.insert x var (ctx_vars ctx) } var
    
    -- Bring a new function into scope.
    bindFun :: Context -> Var -> (Context -> Id -> Fresh a) -> Fresh a
    bindFun ctx x k = do
      name <- freshNamed (globalStr prog x)
      let sig = Signature name (polyType x)
          f tys = applySignature sig tys []
      bindInlineFun ctx x f (\ctx -> k ctx name)

    -- Bring a new inline function into scope.
    bindInlineFun :: Context -> Var -> ([Tip.Type Id] -> Tip.Expr Id) -> (Context -> Fresh a) -> Fresh a
    bindInlineFun ctx x f k =
      k ctx { ctx_funs = Map.insert x f (ctx_funs ctx) }

    -- Bring many new things into scope.
    bindMany ::
      (Context -> a -> (Context -> b -> Fresh c) -> Fresh c) ->
      (Context -> [a] -> (Context -> [b] -> Fresh c) -> Fresh c)
    bindMany bind1 ctx [] k = k ctx []
    bindMany bind1 ctx (x:xs) k =
      bind1 ctx x $ \ctx name ->
        bindMany bind1 ctx xs $ \ctx names ->
          k ctx (name:names)


    -- Type substitution, which (unlike applyTypeInExpr) also substitutes
    -- into the polytypes of globals.
    -- This only makes sense if each type variable is only bound once.
    substTypes :: [Id] -> [Tip.Type Id] -> Tip.Expr Id -> Tip.Expr Id
    substTypes tvs tys e =
      transformBi substGlobal (applyTypeInExpr tvs tys e)
      where
        substGlobal gbl =
          gbl {
            gbl_type = substPolyType (gbl_type gbl) }
        substPolyType PolyType{..} =
          PolyType {
            polytype_tvs  = polytype_tvs,
            polytype_args = map substType polytype_args,
            polytype_res  = substType polytype_res }

        substType ty =
          applyType tvs tys ty

-- Should a given type be erased?
eraseType :: GHC.Type -> Bool
eraseType ty = prop (expandTypeSynonyms ty)
  where
    prop ty
      | isVoidTy ty = True
      | isDictLikeTy ty = True
      | ty `eqType` addrPrimTy = True
      | otherwise = False

-- Predicates which identify special functions and types in GHC.
isAny :: TyCon -> Bool
isAny tc = tc == anyTyCon

----------------------------------------------------------------------
-- Stuff which gets cleaned up at the TIP level.
-- Currently includes removing ErrorId and CastId.
----------------------------------------------------------------------

clean :: Theory Id -> Theory Id
clean thy
  | thy == thy' = thy
  | otherwise = clean thy'
  where
    thy' = clean1 thy

clean1 :: Theory Id -> Theory Id
clean1 thy =
  thy {
    -- Any function whose body is just ErrorId gets replaced by an
    -- uninterpreted function.
    thy_funcs = funcs \\ errors,
    thy_sigs = thy_sigs thy ++ map signature errors,
    thy_asserts = asserts }
  where
    funcs =
      [ func { func_body = freshPass cleanExpr (func_body func) }
      | func <- thy_funcs thy ]
    errors =
      [ func
      | func@Function{func_body = Lcl (Local ErrorId _)} <- funcs ]
    asserts =
      [ form { fm_body = freshPass cleanExpr (fm_body form) }
      | form <- thy_asserts thy ]

cleanExpr :: Tip.Expr Id -> Fresh (Tip.Expr Id)
cleanExpr = transformBiM $ \e ->
  let
    err = return (Lcl (Local ErrorId (Tip.exprType e)))
    isError (Lcl (Local ErrorId _)) = True
    isError _ = False in
  case e of
    -- CastId ==> \x -> x
    -- or
    -- CastId ==> \x -> Widen x
    Lcl (Local CastId ([arg] :=>: res)) -> do
      x <- freshLocal arg
      return $
        Tip.Lam [x] $
        if arg == res then Lcl x else Builtin NumWiden :@: [Lcl x]

    -- We just pull ErrorId to the top level as far as possible.
    -- If a branch of a case is an ErrorId, that branch is deleted.
    f :@: args | any isError args -> err
    Tip.Lam _ e | isError e -> err
    Tip.Let x t u | isError t -> (t // x) u
    Tip.Let x t u | isError u -> err
    Tip.Quant _ _ _ e | isError e -> err
    Tip.Match e alts | isError e -> err
    Tip.Match e alts ->
      case filter (not . isError . case_rhs) alts of
        [] -> err
        alts' -> return (Tip.Match e alts')
    _ -> return e

----------------------------------------------------------------------
-- Debug output.
----------------------------------------------------------------------

showOutputable :: Outputable a => a -> String
showOutputable = showSDocUnsafe . ppr

pprRecord :: [(String, SDoc)] -> SDoc
pprRecord fields = braces (pprWithCommas pprField fields)
  where
    pprField (name, value) = hang (text name <+> equals) 2 value

instance Outputable TipAnnotation where
  ppr = text . show

instance Outputable Program where
  ppr Program{..} =
    pprRecord [("types", ppr prog_types), ("globals", ppr prog_globals)]

instance Outputable GlobalInfo where
  ppr ConInfo{..} =
    pprRecord [
      ("args", ppr global_args),
      ("res", ppr global_res),
      ("tycon", ppr global_tycon),
      ("annotations", ppr global_annotations)]
  ppr FunInfo{..} =
    pprRecord [("definition", ppr global_definition), ("annotations", ppr global_annotations)]

instance Outputable TypeInfo where
  ppr TypeInfo{..} =
    pprRecord [
      ("tvs", ppr type_tvs),
      ("constructors", ppr type_constructors),
      ("annotations", ppr type_annotations)]

instance Outputable Id where
  ppr (TypeId _ ty) = ppr ty
  ppr (GlobalId _ x) = ppr x
  ppr (LocalId _ n) = text "local" <> ppr n
  ppr (ProjectionId _ x n) = ppr x <> text "/" <> ppr n
  ppr (DiscriminatorId _ x) = ppr x <> text "?"
  ppr x = text (varStr x)

instance Outputable SDoc where
  ppr = id

data ContextError e = ContextError String e deriving Typeable

instance Exception e => Exception (ContextError e) where
  displayException (ContextError msg e) =
    unlines $
      lines msg ++
      [""] ++
      lines (displayException e)

instance Exception e => Show (ContextError e) where
  show = displayException

inContext :: String -> a -> a
inContext msg x =
  mapException (\(e :: SomeException) -> ContextError msg e) x

inContextM :: String -> Fresh a -> Fresh a
inContextM msg (Fresh x) =
  Fresh $ state $ \s ->
    inContext msg (runState x s)
