{-# LANGUAGE RecordWildCards #-}
module Tip.Haskell.Translate where

import Tip.Haskell.Repr as H
import Tip.Core as T hiding (Formula(..))
import qualified Tip.Core as T

class Ord a => HaskellVar a where
  prelude :: String -> a
  tip_dsl :: String -> a
  prop_id :: Int -> a

trTheory :: HaskellVar a => Theory a -> Decls a
trTheory Theory{..} =
  Decls $
    map trDatatype thy_datatypes ++
    map trSort thy_sorts ++
    map trSig thy_sigs ++
    concatMap trFunc thy_funcs ++
    zipWith trAssert [0..] thy_asserts

trDatatype :: HaskellVar a => Datatype a -> Decl a
trDatatype (Datatype tc tvs cons) =
  DataDecl tc tvs
    [ (c,map (trType . snd) args) | Constructor c _ args <- cons ]
    (map prelude ["Eq","Ord","Show"])

trSort :: HaskellVar a => Sort a -> Decl a
trSort (Sort _s _i) = error "trSort"

trSig :: HaskellVar a => Signature a -> Decl a
trSig (Signature _f _t) = error "trSig"

trFunc :: HaskellVar a => Function a -> [Decl a]
trFunc fn@Function{..}
    = [ TySig func_name [] (trPolyType (funcType fn))
      , FunDecl
          func_name
          [ (map trDeepPattern dps,trExpr Expr rhs)
          | (dps,rhs) <- patternMatchingView func_args func_body
          ]
      ]

trAssert :: HaskellVar a => Int -> T.Formula a -> Decl a
trAssert i (T.Formula r _ b) = funDecl (prop_id i) [] (assume (trExpr Formula b))
  where
  assume e =
    case r of
      Prove  -> e
      Assert -> Apply (tip_dsl "assume") [e]

trDeepPattern :: HaskellVar a => DeepPattern a -> H.Pat a
trDeepPattern (DeepConPat Global{..} dps) = H.ConPat gbl_name (map trDeepPattern dps)
trDeepPattern (DeepVarPat Local{..})      = VarPat lcl_name
trDeepPattern (DeepLitPat (T.Int i))      = IntPat i
trDeepPattern (DeepLitPat (Bool b))       = withBool H.ConPat b

trPattern :: HaskellVar a => T.Pattern a -> H.Pat a
trPattern Default = WildPat
trPattern (T.ConPat Global{..} xs) = H.ConPat gbl_name (map (VarPat . lcl_name) xs)
trPattern (T.LitPat (T.Int i))     = H.IntPat i
trPattern (T.LitPat (Bool b))      = withBool H.ConPat b

trExpr :: HaskellVar a => Kind -> T.Expr a -> H.Expr a
trExpr k e0 =
  case e0 of
    Builtin (Lit (T.Int i)) :@: [] -> H.Int i
    Builtin (Lit (Bool b)) :@: []  -> withBool Apply b
    hd :@: es -> let (f,k') = trHead k hd
                 in Apply f (map (trExpr k') es)
    Lcl x -> var (lcl_name x)
    T.Lam xs b  -> H.Lam (map (VarPat . lcl_name) xs) (trExpr Expr b)
    Match e alts -> H.Case (trExpr Expr e) [ (trPattern p,trExpr Expr rhs) | T.Case p rhs <- alts ]
    T.Let x e b -> H.Let (lcl_name x) (trExpr Expr e) (trExpr k b)
    T.Quant _ q xs b ->
      foldr
        (\ x e ->
            Apply (tip_dsl (case q of Forall -> "forAll"; Exists -> "exists"))
              [H.Lam [VarPat (lcl_name x)] e])
        (trExpr Formula b)
        xs

trHead :: HaskellVar a => Kind -> T.Head a -> (a,Kind)
trHead k (Gbl Global{..}) = (gbl_name,Expr)
trHead k (Builtin b)      = trBuiltin k b

data Kind = Expr | Formula deriving Eq

trBuiltin :: HaskellVar a => Kind -> T.Builtin -> (a,Kind)
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
    IntGe     -> prelude' "=>"
    IntLt     -> prelude' "<"
    IntLe     -> prelude' "<="
  where
  prelude' s = (prelude s,Expr)

  case_kind se sf =
    case k of
      Expr    -> prelude' se
      Formula -> (tip_dsl sf,Formula)

trType :: HaskellVar a => T.Type a -> H.Type a
trType (T.TyVar x)     = H.TyVar x
trType (T.TyCon tc ts) = H.TyCon tc (map trType ts)
trType (ts :=>: t)     = foldr TyArr (trType t) (map trType ts)
trType (BuiltinType Integer) = H.TyCon (prelude "Int") []
trType (BuiltinType Boolean) = H.TyCon (prelude "Bool") []

-- ignores the type variables
trPolyType :: HaskellVar a => T.PolyType a -> H.Type a
trPolyType (PolyType _ ts t) = trType (ts :=>: t)

withBool :: HaskellVar a => (a -> [c] -> b) -> Bool -> b
withBool k b = k (prelude (if b then "True" else "False")) []

