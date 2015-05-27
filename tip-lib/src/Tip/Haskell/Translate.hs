{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
module Tip.Haskell.Translate where

#include "errors.h"
import Tip.Haskell.Repr as H
import Tip.Core as T hiding (Formula(..),globals)
import qualified Tip.Core as T
import Tip.Pretty
import Tip.Fresh
import Tip.Utils
import Tip.Scope

import Control.Monad

import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import qualified Data.Map as M

import Data.Generics.Geniplate

prelude :: String -> HsId a
prelude = Qualified "Prelude"

tipDSL :: String -> HsId a
tipDSL = Qualified "Tip"

quickCheck :: String -> HsId a
quickCheck = Qualified "Test.QuickCheck"

quickCheckAll :: String -> HsId a
quickCheckAll = Qualified "Test.QuickCheck.All"

quickSpec :: String -> HsId a
quickSpec = Qualified "QuickSpec"

feat :: String -> HsId a
feat = Qualified "Test.Feat"

typeable :: String -> HsId a
typeable = Qualified "Data.Typeable"

data HsId a
    = Qualified String String
    | Other a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

instance PrettyVar a => PrettyVar (HsId a) where
  varStr (Qualified m s) = m ++ "." ++ s
  varStr (Other x)       = varStr x

instance Name a => Name (HsId a) where
  fresh      = fmap Other fresh
  freshNamed = fmap Other . freshNamed
  getUnique Qualified{} = 0
  getUnique (Other x)   = getUnique x

addHeader :: Decls a -> Decls a
addHeader (Decls ds) =
    Decls (map LANGUAGE ["TemplateHaskell","DeriveDataTypeable","TypeOperators"] ++ Module "A" : ds)

addImports :: Ord a => Decls (HsId a) -> Decls (HsId a)
addImports d@(Decls ds) = Decls (QualImport "Text.Show.Functions" : imps ++ ds)
  where
  imps = usort [ QualImport m | Qualified m _ <- F.toList d ]

trTheory :: Name a => Theory a -> Fresh (Decls (HsId a))
trTheory = trTheory' . fmap Other

trTheory' :: (a ~ HsId b,Name b) => Theory a -> Fresh (Decls a)
trTheory' thy@Theory{..} =
  do asserts <- trAsserts thy_asserts
     sig <- makeSig thy
     return $
       Decls $
         concatMap trDatatype thy_datatypes ++
         map trSort thy_sorts ++
         map trSig thy_sigs ++
         concatMap trFunc thy_funcs ++
         asserts ++
         [sig]

trDatatype :: (a ~ HsId b) => Datatype a -> [Decl a]
trDatatype (Datatype tc tvs cons) =
  [ DataDecl tc tvs
      [ (c,map (trType . snd) args) | Constructor c _ args <- cons ]
      (map prelude ["Eq","Ord","Show"] ++ [typeable "Typeable"])
  , TH (Apply (feat "deriveEnumerable") [QuoteTyCon tc])
  , InstDecl [H.TyCon (feat "Enumerable") [H.TyVar a] | a <- tvs]
             (H.TyCon (quickCheck "Arbitrary") [H.TyCon tc (map H.TyVar tvs)])
             [funDecl
                (quickCheck "arbitrary") []
                (Apply (quickCheck "sized") [Apply (feat "uniform") []])]
  ]

trSort :: (a ~ HsId b) => Sort a -> Decl a
trSort (Sort _s _i) = error "trSort"

trSig :: (a ~ HsId b) => Signature a -> Decl a
trSig (Signature _f _t) = error "trSig"

trFunc :: (a ~ HsId b,Ord b) => Function a -> [Decl a]
trFunc fn@Function{..}
    = [ TySig func_name [] (trPolyType (funcType fn))
      , FunDecl
          func_name
          [ (map trDeepPattern dps,trExpr Expr rhs)
          | (dps,rhs) <- patternMatchingView func_args func_body
          ]
      ]

trAsserts :: (a ~ HsId b,Name b) => [T.Formula a] -> Fresh [Decl a]
trAsserts fms =
  do (names,decls) <- mapAndUnzipM trAssert fms
     main <- freshNamed "main"
     return $ decls ++
       [ TH (Apply (prelude "return") [List []])
       , funDecl main []
           (mkDo [ Stmt (THSplice (Apply (quickCheckAll "polyQuickCheck")
                                         [QuoteName name]))
                 | name <- names ]
                 Noop)
       ]

trAssert :: (a ~ HsId b,Name b) => T.Formula a -> Fresh (a,Decl a)
trAssert (T.Formula r _ b) =
  do prop_name <- freshNamed "prop"
     return (prop_name,funDecl prop_name args (assume (trExpr Formula body)))
  where
  (args,body) =
    case b of
      Quant _ Forall lcls term -> (map lcl_name lcls,term)
      _                        -> ([],b)

  assume e =
    case r of
      Prove  -> e
      Assert -> Apply (tipDSL "assume") [e]

trDeepPattern :: (a ~ HsId b) => DeepPattern a -> H.Pat a
trDeepPattern (DeepConPat Global{..} dps) = H.ConPat gbl_name (map trDeepPattern dps)
trDeepPattern (DeepVarPat Local{..})      = VarPat lcl_name
trDeepPattern (DeepLitPat (T.Int i))      = IntPat i
trDeepPattern (DeepLitPat (Bool b))       = withBool H.ConPat b

trPattern :: (a ~ HsId b) => T.Pattern a -> H.Pat a
trPattern Default = WildPat
trPattern (T.ConPat Global{..} xs) = H.ConPat gbl_name (map (VarPat . lcl_name) xs)
trPattern (T.LitPat (T.Int i))     = H.IntPat i
trPattern (T.LitPat (Bool b))      = withBool H.ConPat b

trExpr :: (a ~ HsId b) => Kind -> T.Expr a -> H.Expr a
trExpr k e0 =
  case e0 of
    Builtin (Lit (T.Int i)) :@: [] -> H.Int i
    Builtin (Lit (Bool b)) :@: []  -> withBool Apply b
    hd :@: es -> let (f,k') = trHead k hd
                 in Apply f (map (trExpr k') es)
    Lcl x -> var (lcl_name x)
    T.Lam xs b  -> H.Lam (map (VarPat . lcl_name) xs) (trExpr Expr b)
    Match e alts -> H.Case (trExpr Expr e) [ (trPattern p,trExpr Expr rhs) | T.Case p rhs <- default_last alts ]
    T.Let x e b -> H.Let (lcl_name x) (trExpr Expr e) (trExpr k b)
    T.Quant _ q xs b ->
      foldr
        (\ x e ->
            Apply (tipDSL (case q of Forall -> "forAll"; Exists -> "exists"))
              [H.Lam [VarPat (lcl_name x)] e])
        (trExpr Formula b)
        xs

  where
  default_last (def@(T.Case Default _):alts) = alts ++ [def]
  default_last alts = alts

trHead :: (a ~ HsId b) => Kind -> T.Head a -> (a,Kind)
trHead k (Gbl Global{..}) = (gbl_name,Expr)
trHead k (Builtin b)      = trBuiltin k b

data Kind = Expr | Formula deriving Eq

trBuiltin :: (a ~ HsId b) => Kind -> T.Builtin -> (a,Kind)
trBuiltin k b =
  case b of
    At        -> (prelude "id",Expr)
    Lit{}     -> error "trBuiltin"
    And       -> case_kind ".&&."
    Or        -> case_kind ".||."
    Not       -> case_kind "neg"
    Implies   -> case_kind "==>"
    Equal     -> case_kind "==="
    Distinct  -> case_kind "=/="
    _         -> prelude_fn
  where
  Just prelude_str = lookup b hsBuiltins
  prelude_fn = (prelude prelude_str,Expr)

  case_kind sf =
    case k of
      Expr    -> prelude_fn
      Formula -> (tipDSL sf,Formula)

trType :: (a ~ HsId b) => T.Type a -> H.Type a
trType (T.TyVar x)     = H.TyVar x
trType (T.TyCon tc ts) = H.TyCon tc (map trType ts)
trType (ts :=>: t)     = foldr TyArr (trType t) (map trType ts)
trType (BuiltinType b) = trBuiltinType b

trBuiltinType :: BuiltinType -> H.Type (HsId a)
trBuiltinType Integer = H.TyCon (prelude "Int") []
trBuiltinType Boolean = H.TyCon (prelude "Bool") []

-- ignores the type variables
trPolyType :: (a ~ HsId b) => T.PolyType a -> H.Type a
trPolyType (PolyType _ ts t) = trType (ts :=>: t)

withBool :: (a ~ HsId b) => (a -> [c] -> d) -> Bool -> d
withBool k b = k (prelude (if b then "True" else "False")) []

-- * Builtins

hsBuiltins :: [(T.Builtin,String)]
hsBuiltins =
  [ (And      , "&&" )
  , (Or       , "||" )
  , (Not      , "not")
  , (Implies  , "<=" )
  , (Equal    , "==" )
  , (Distinct , "/=" )
  , (IntAdd   , "+"  )
  , (IntSub   , "-"  )
  , (IntMul   , "*"  )
  , (IntDiv   , "div")
  , (IntMod   , "mod")
  , (IntGt    , ">"  )
  , (IntGe    , ">=" )
  , (IntLt    , "<"  )
  , (IntLe    , "<=" )
  ]

typeOfBuiltin :: Builtin -> T.Type a
typeOfBuiltin b = case b of
  And      -> bbb
  Or       -> bbb
  Not      -> bbb
  Implies  -> bbb
  Equal    -> bbb -- ?
  Distinct -> bbb -- ?
  IntAdd   -> iii
  IntSub   -> iii
  IntMul   -> iii
  IntDiv   -> iii
  IntMod   -> iii
  IntGt    -> iib
  IntGe    -> iib
  IntLt    -> iib
  IntLe    -> iib
  _        -> __
  where
  bbb = [boolType,boolType] :=>: boolType
  iii = [intType,intType] :=>: intType
  iib = [intType,intType] :=>: boolType


-- * QuickSpec signatures

makeSig :: (Ord a,Name a) => Theory (HsId a) -> Fresh (Decl (HsId a))
makeSig thy =
  do sig_name <- freshNamed "sig"
     return (makeSig' sig_name thy)

makeSig' :: forall a . (PrettyVar a,Ord a) => HsId a -> Theory (HsId a) -> Decl (HsId a)
makeSig' sig_name thy@Theory{..} =
  funDecl sig_name [] $
    Apply (quickSpec "signature") [] `Record`
      [ (quickSpec "constants", List
           [ Apply (quickSpec "constant")
               [H.String f,Apply f [] ::: qsType t]
           | (f,t) <- constants ])
      , (quickSpec "instances", List
           [ Apply (quickSpec ("inst" ++ concat [ show (length tys) | length tys >= 2 ]))
               [ Apply (quickSpec "Sub") [Apply (quickSpec "Dict") []] :::
                 H.TyCon (quickSpec ":-") [TyTup (map (cl c1) tys),cl c2 (H.TyCon t tys)]]
           | (t,n) <- type_univ
           , (c1, c2) <- [(prelude "Ord", prelude "Ord"),
                          (feat "Enumerable", feat "Enumerable"),
                          (feat "Enumerable",quickCheck "Arbitrary")]
           , let cl c x = H.TyCon c [x]
           , let tys = map trType (qsTvs n)
           ])
      ]
  where
    scp = scope thy

    poly_type (PolyType _ args res) = args :=>: res

    constants =
      [ (f,poly_type (globalType g))
      | (f,g) <- M.toList (globals scp)
      , case g of
          ConstructorInfo{} -> True
          FunctionInfo{}    -> True
          _                 -> False
      ] ++
      [ (prelude s,typeOfBuiltin b)
      | b <- theoryBuiltins thy
      , Just s <- [lookup b hsBuiltins]
      ]

    type_univ =
      [ (data_name, length data_tvs)
      | (_,DatatypeInfo Datatype{..}) <- M.toList (types scp)
      ]

qsType :: Ord a => T.Type (HsId a) -> H.Type (HsId a)
qsType t = trType (applyType tvs (qsTvs (length tvs)) t)
  where tvs = tyVars t

qsTvs :: Int -> [T.Type (HsId a)]
qsTvs n = take n (cycle [ T.TyCon (quickSpec qs_tv) [] | qs_tv <- ["A","B","C","D","E"] ])

theoryBuiltins :: Ord a => Theory a -> [T.Builtin]
theoryBuiltins = usort . universeBi

