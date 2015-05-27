{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
module Tip.Haskell.Translate where

import Tip.Haskell.Repr as H
import Tip.Core as T hiding (Formula(..))
import qualified Tip.Core as T
import Tip.Pretty
import Tip.Fresh
import Tip.Utils

import Control.Monad

import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

prelude :: String -> HsId a
prelude = Qualified "Prelude"

tipDSL :: String -> HsId a
tipDSL = Qualified "Tip"

quickCheck :: String -> HsId a
quickCheck = Qualified "Test.QuickCheck"

quickCheckAll :: String -> HsId a
quickCheckAll = Qualified "Test.QuickCheck.All"

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
    Decls (map LANGUAGE ["TemplateHaskell","DeriveDataTypeable"] ++ Module "A" : ds)

addImports :: Ord a => Decls (HsId a) -> Decls (HsId a)
addImports d@(Decls ds) = Decls (imps ++ ds)
  where
  imps = usort [ QualImport m | Qualified m _ <- F.toList d ]

trTheory :: Name a => Theory a -> Fresh (Decls (HsId a))
trTheory = trTheory' . fmap Other

trTheory' :: (a ~ HsId b,Name b) => Theory a -> Fresh (Decls a)
trTheory' Theory{..} =
  do asserts <- trAsserts thy_asserts
     return $
       Decls $
         concatMap trDatatype thy_datatypes ++
         map trSort thy_sorts ++
         map trSig thy_sigs ++
         concatMap trFunc thy_funcs ++
         asserts

trDatatype :: (a ~ HsId b,Name b) => Datatype a -> [Decl a]
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

trSort :: (a ~ HsId b,Name b) => Sort a -> Decl a
trSort (Sort _s _i) = error "trSort"

trSig :: (a ~ HsId b,Name b) => Signature a -> Decl a
trSig (Signature _f _t) = error "trSig"

trFunc :: (a ~ HsId b,Name b) => Function a -> [Decl a]
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

trDeepPattern :: (a ~ HsId b,Name b) => DeepPattern a -> H.Pat a
trDeepPattern (DeepConPat Global{..} dps) = H.ConPat gbl_name (map trDeepPattern dps)
trDeepPattern (DeepVarPat Local{..})      = VarPat lcl_name
trDeepPattern (DeepLitPat (T.Int i))      = IntPat i
trDeepPattern (DeepLitPat (Bool b))       = withBool H.ConPat b

trPattern :: (a ~ HsId b,Name b) => T.Pattern a -> H.Pat a
trPattern Default = WildPat
trPattern (T.ConPat Global{..} xs) = H.ConPat gbl_name (map (VarPat . lcl_name) xs)
trPattern (T.LitPat (T.Int i))     = H.IntPat i
trPattern (T.LitPat (Bool b))      = withBool H.ConPat b

trExpr :: (a ~ HsId b,Name b) => Kind -> T.Expr a -> H.Expr a
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

trHead :: (a ~ HsId b,Name b) => Kind -> T.Head a -> (a,Kind)
trHead k (Gbl Global{..}) = (gbl_name,Expr)
trHead k (Builtin b)      = trBuiltin k b

data Kind = Expr | Formula deriving Eq

trBuiltin :: (a ~ HsId b,Name b) => Kind -> T.Builtin -> (a,Kind)
trBuiltin k b =
  case b of
    At        -> prelude' "id"
    Lit{}     -> error "trBuiltin"
    And       -> case_kind "&&" ".&&."
    Or        -> case_kind "||" ".||."
    Not       -> case_kind "not" "neg"
    Implies   -> case_kind "<=" "==>"
    Equal     -> case_kind "==" "==="
    Distinct  -> case_kind "/=" "=/="
    IntAdd    -> prelude' "+"
    IntSub    -> prelude' "-"
    IntMul    -> prelude' "*"
    IntDiv    -> prelude' "div"
    IntMod    -> prelude' "mod"
    IntGt     -> prelude' ">"
    IntGe     -> prelude' ">="
    IntLt     -> prelude' "<"
    IntLe     -> prelude' "<="
  where
  prelude' s = (prelude s,Expr)

  case_kind se sf =
    case k of
      Expr    -> prelude' se
      Formula -> (tipDSL sf,Formula)

trType :: (a ~ HsId b,Name b) => T.Type a -> H.Type a
trType (T.TyVar x)     = H.TyVar x
trType (T.TyCon tc ts) = H.TyCon tc (map trType ts)
trType (ts :=>: t)     = foldr TyArr (trType t) (map trType ts)
trType (BuiltinType Integer) = H.TyCon (prelude "Int") []
trType (BuiltinType Boolean) = H.TyCon (prelude "Bool") []

-- ignores the type variables
trPolyType :: (a ~ HsId b,Name b) => T.PolyType a -> H.Type a
trPolyType (PolyType _ ts t) = trType (ts :=>: t)

withBool :: (a ~ HsId b,Name b) => (a -> [c] -> d) -> Bool -> d
withBool k b = k (prelude (if b then "True" else "False")) []

