{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE RecordWildCards #-}
module Tip.Haskell.Translate where

import Tip.Haskell.Repr as H
import Tip.Core as T hiding (Formula(..))
import qualified Tip.Core as T
import Tip.Pretty
import Tip.Fresh

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

-- | This type class is pretty stupid.
-- It should probably be replaced with HsId directly
class Name a => TranslatableVar a where
  prelude :: String -> a
  tip_dsl :: String -> a

data HsId a
    = Qualified String String
    | Other a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

instance PrettyVar a => PrettyVar (HsId a) where
  varStr (Qualified m s) = m ++ "." ++ s
  varStr (Other x)       = varStr x

instance PrettyVar a => PrettyHsVar (HsId a) where
  varUnqual (Qualified _ s) = s
  varUnqual v               = varStr v

instance Name a => TranslatableVar (HsId a) where
  prelude = Qualified "Prelude"
  tip_dsl = Qualified "Tip"

instance Name a => Name (HsId a) where
  fresh      = fmap Other fresh
  freshNamed = fmap Other . freshNamed
  getUnique Qualified{} = 0
  getUnique (Other x)   = getUnique x

trTheory :: Name a => Theory a -> Fresh (Decls (HsId a))
trTheory = trTheory' . fmap Other

trTheory' :: TranslatableVar a => Theory a -> Fresh (Decls a)
trTheory' Theory{..} =
  do asserts <- mapM trAssert thy_asserts
     return $
       Decls $
         map trDatatype thy_datatypes ++
         map trSort thy_sorts ++
         map trSig thy_sigs ++
         concatMap trFunc thy_funcs ++
         asserts

trDatatype :: TranslatableVar a => Datatype a -> Decl a
trDatatype (Datatype tc tvs cons) =
  DataDecl tc tvs
    [ (c,map (trType . snd) args) | Constructor c _ args <- cons ]
    (map prelude ["Eq","Ord","Show"])

trSort :: TranslatableVar a => Sort a -> Decl a
trSort (Sort _s _i) = error "trSort"

trSig :: TranslatableVar a => Signature a -> Decl a
trSig (Signature _f _t) = error "trSig"

trFunc :: TranslatableVar a => Function a -> [Decl a]
trFunc fn@Function{..}
    = [ TySig func_name [] (trPolyType (funcType fn))
      , FunDecl
          func_name
          [ (map trDeepPattern dps,trExpr Expr rhs)
          | (dps,rhs) <- patternMatchingView func_args func_body
          ]
      ]

trAssert :: TranslatableVar a => T.Formula a -> Fresh (Decl a)
trAssert (T.Formula r _ b) =
  do prop_name <- freshNamed "prop"
     return (funDecl prop_name [] (assume (trExpr Formula b)))
  where
  assume e =
    case r of
      Prove  -> e
      Assert -> Apply (tip_dsl "assume") [e]

trDeepPattern :: TranslatableVar a => DeepPattern a -> H.Pat a
trDeepPattern (DeepConPat Global{..} dps) = H.ConPat gbl_name (map trDeepPattern dps)
trDeepPattern (DeepVarPat Local{..})      = VarPat lcl_name
trDeepPattern (DeepLitPat (T.Int i))      = IntPat i
trDeepPattern (DeepLitPat (Bool b))       = withBool H.ConPat b

trPattern :: TranslatableVar a => T.Pattern a -> H.Pat a
trPattern Default = WildPat
trPattern (T.ConPat Global{..} xs) = H.ConPat gbl_name (map (VarPat . lcl_name) xs)
trPattern (T.LitPat (T.Int i))     = H.IntPat i
trPattern (T.LitPat (Bool b))      = withBool H.ConPat b

trExpr :: TranslatableVar a => Kind -> T.Expr a -> H.Expr a
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
            Apply (tip_dsl (case q of Forall -> "forAll"; Exists -> "exists"))
              [H.Lam [VarPat (lcl_name x)] e])
        (trExpr Formula b)
        xs

  where
  default_last (def@(T.Case Default _):alts) = alts ++ [def]
  default_last alts = alts

trHead :: TranslatableVar a => Kind -> T.Head a -> (a,Kind)
trHead k (Gbl Global{..}) = (gbl_name,Expr)
trHead k (Builtin b)      = trBuiltin k b

data Kind = Expr | Formula deriving Eq

trBuiltin :: TranslatableVar a => Kind -> T.Builtin -> (a,Kind)
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

trType :: TranslatableVar a => T.Type a -> H.Type a
trType (T.TyVar x)     = H.TyVar x
trType (T.TyCon tc ts) = H.TyCon tc (map trType ts)
trType (ts :=>: t)     = foldr TyArr (trType t) (map trType ts)
trType (BuiltinType Integer) = H.TyCon (prelude "Int") []
trType (BuiltinType Boolean) = H.TyCon (prelude "Bool") []

-- ignores the type variables
trPolyType :: TranslatableVar a => T.PolyType a -> H.Type a
trPolyType (PolyType _ ts t) = trType (ts :=>: t)

withBool :: TranslatableVar a => (a -> [c] -> b) -> Bool -> b
withBool k b = k (prelude (if b then "True" else "False")) []

