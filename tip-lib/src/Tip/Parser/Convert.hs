module Tip.Parser.Convert where

import Tip.Parser.AbsTIP as A -- from A ...
import Tip               as T -- ... to T
import Tip.Pretty
import Text.PrettyPrint hiding (int)

import Data.List
import Data.Function

data Id = Id
  { idString :: String
  , idPos    :: (Int,Int)
  }
  deriving Show

instance Eq Id where
  (==) = (==) `on` idString

instance Ord Id where
  compare = compare `on` idString

instance Pretty Id where
  pp (Id s _) = text s

trSymbol :: Symbol -> Id
trSymbol (Symbol (p,s)) = Id s p

trLocal :: Symbol -> Local Id
trLocal s = Local (trSymbol s) NoType

trGlobal :: Symbol -> Global Id
trGlobal s = Global (trSymbol s) NoPolyType []

trDecl :: Decl -> Theory Id
trDecl x = case x of
  DeclareDatatypes tvs datatypes -> emptyTheory { thy_data_decls = map (trDatatype (map trSymbol tvs)) datatypes }
  DeclareSort s 0 -> emptyTheory { thy_abs_type_decls = [AbsType (trSymbol s)] }
  DeclareSort s n -> error $ "Sort with kind " ++ show n
  DeclareFun fundecl -> emptyTheory { thy_abs_func_decls = [trFunDecl fundecl] }
  DefineFun fundefs  -> emptyTheory { thy_func_decls = map trFunDef fundefs }
  MonoAssert expr    -> trDecl (ParAssert [] expr)
  ParAssert tvs expr -> emptyTheory { thy_form_decls = [Formula Assert (map trSymbol tvs) (trExpr expr)] }


trFunDef :: FunDef -> T.Function Id
trFunDef x = case x of
  MonoFunDef inner -> trFunDef (ParFunDef [] inner)
  ParFunDef tvs (InnerFunDef f bindings res_type body) ->
    Function (trSymbol f) (map trSymbol tvs)
             (map trLocalBinding bindings) (trType res_type)
             (trExpr body)

trFunDecl :: FunDecl -> T.AbsFunc Id
trFunDecl x = case x of
  MonoFunDecl inner -> trFunDecl (ParFunDecl [] inner)
  ParFunDecl tvs (InnerFunDecl f args res) ->
    AbsFunc (trSymbol f) (PolyType (map trSymbol tvs) (map trType args) (trType res))


trDatatype :: [Id] -> A.Datatype -> T.Datatype Id
trDatatype tvs (A.Datatype s constructors) =
  T.Datatype (trSymbol s) tvs (map trConstructor constructors)

trConstructor :: A.Constructor -> T.Constructor Id
trConstructor (A.Constructor s args) =
  T.Constructor name name{ idString = "is-" ++ idString name } (map trBinding args)
 where name = trSymbol s

trBinding :: Binding -> (Id,T.Type Id)
trBinding (Binding s t) = (trSymbol s,trType t)

trLocalBinding :: Binding -> Local Id
trLocalBinding = uncurry Local . trBinding


trLetDecl :: LetDecl -> T.Expr Id -> T.Expr Id
trLetDecl (LetDecl binding expr) = T.Let (trLocalBinding binding) (trExpr expr)


trExpr :: A.Expr -> T.Expr Id
trExpr e0 = case e0 of
  A.Var s             -> Lcl (trLocal s) -- (or global constant)
  A.App head exprs    -> trHead head (map trExpr exprs)
  A.Match expr cases  -> T.Match (trExpr expr) (sort (map trCase cases))
  A.Let letdecls expr -> foldr trLetDecl (trExpr expr) letdecls
  A.Binder binder bindings expr -> trBinder binder (map trLocalBinding bindings) (trExpr expr)
  A.LitInt n -> intLit n
  A.LitTrue  -> bool True
  A.LitFalse -> bool False

trHead :: A.Head -> [T.Expr Id] -> T.Expr Id
trHead A.IfThenElse [c,t,f] = makeIf c t f
trHead A.IfThenElse args    = error $ "if-then-else with " ++ show (length args) ++ " arguments"
trHead (A.Const s)  args    = Gbl (trGlobal s) :@: args
trHead x args = Builtin b :@: args
 where
  b = case x of
    A.At       -> T.At 0
    A.And      -> T.And
    A.Or       -> T.Or
    A.Not      -> T.Not
    A.Implies  -> T.Implies
    A.Equal    -> T.Equal
    A.Distinct -> T.Distinct
    A.IntAdd   -> T.IntAdd
    A.IntSub   -> T.IntSub
    A.IntMul   -> T.IntMul
    A.IntGt    -> T.IntGt
    A.IntGe    -> T.IntGe
    A.IntLt    -> T.IntLt
    A.IntLe    -> T.IntLe


trBinder :: A.Binder -> [Local Id] -> T.Expr Id -> T.Expr Id
trBinder b = case b of
  A.Lambda -> T.Lam
  A.Forall -> mkQuant T.Forall
  A.Exists -> mkQuant T.Exists

trCase :: A.Case -> T.Case Id
trCase (A.Case pattern expr) = T.Case (trPattern pattern) (trExpr expr)

trPattern :: A.Pattern -> T.Pattern Id
trPattern p = case p of
  A.Default        -> T.Default
  A.ConPat s bound -> T.ConPat (trGlobal s) (map trLocal bound)
  A.SimplePat s    -> T.ConPat (trGlobal s) []


trType :: A.Type -> T.Type Id
trType t0 = case t0 of
  A.TyVar s    -> T.TyVar (trSymbol s)
  A.TyApp s ts -> T.TyCon (trSymbol s) (map trType ts)
  A.ArrowTy ts -> map trType (init ts) :=>: trType (last ts)
  A.IntTy      -> intType
  A.BoolTy     -> boolType

