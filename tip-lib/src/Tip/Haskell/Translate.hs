{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
module Tip.Haskell.Translate where

#include "errors.h"
import Tip.Haskell.Repr as H
import Tip.Core as T hiding (Formula(..),globals,Type(..),Decl(..))
import Tip.Core (Type((:=>:),BuiltinType))
import qualified Tip.Core as T
import Tip.Pretty
import Tip.Utils
import Tip.Scope

import Data.Maybe (isNothing)

import Tip.CallGraph

import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import qualified Data.Map as M

import Data.Generics.Geniplate

import Data.List (nub,partition)

import Tip.Haskell.Observers

prelude :: String -> HsId a
prelude = Qualified "Prelude" (Just "P")

ratio :: String -> HsId a
ratio = Qualified "Data.Ratio" (Just "R")

tipDSL :: String -> HsId a
tipDSL = Qualified "Tip" Nothing

quickCheck :: String -> HsId a
quickCheck = Qualified "Test.QuickCheck" (Just "QC")

quickCheckUnsafe :: String -> HsId a
quickCheckUnsafe = Qualified "Test.QuickCheck.Gen.Unsafe" (Just "QU")

quickCheckAll :: String -> HsId a
quickCheckAll = Qualified "Test.QuickCheck.All" (Just "QC")

quickSpec :: String -> HsId a
quickSpec = Qualified "QuickSpec" (Just "QS")

sysEnv :: String -> HsId a
sysEnv = Qualified "System.Environment" (Just "Env")

smtenSym :: String -> HsId a
smtenSym = Qualified "Smten.Symbolic" (Just "S")

smtenEnv :: String -> HsId a
smtenEnv = Qualified "Smten.System.Environment" (Just "Env")

smtenMinisat :: String -> HsId a
smtenMinisat = Qualified "Smten.Symbolic.Solver.MiniSat" (Just "S")

smtenMonad :: String -> HsId a
smtenMonad = Qualified "Smten.Control.Monad" (Just "S")

-- smten also needs Prelude to be replaced with Smten.Prelude

feat :: String -> HsId a
feat = Qualified "Test.Feat" (Just "F")

lsc :: String -> HsId a
lsc = Qualified "Test.LazySmallCheck" (Just "L")

typeable :: String -> HsId a
typeable = Qualified "Data.Typeable" (Just "T")

data HsId a
    = Qualified
         { qual_module       :: String
         , qual_module_short :: Maybe String
         , qual_func         :: String
         }
    -- ^ A qualified import
    | Exact String
    -- ^ The current module defines something with this very important name
    | Other a
    -- ^ From the theory
    | Derived (HsId a) String
    -- ^ For various purposes...
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

instance PrettyVar a => PrettyVar (HsId a) where
  varStr (Qualified _ (Just m) s) = m ++ "." ++ s
  varStr (Qualified m Nothing  s) = m ++ "." ++ s
  varStr (Exact s) = s
  varStr (Other x) = varStr x
  varStr (Derived o s) = s ++ varStr o

addHeader :: String -> Decls a -> Decls a
addHeader mod_name (Decls ds) =
    Decls (map LANGUAGE ["TemplateHaskell","DeriveDataTypeable","TypeOperators","ImplicitParams","RankNTypes"] ++ Module mod_name : ds)

addImports :: Ord a => Decls (HsId a) -> Decls (HsId a)
addImports d@(Decls ds) = Decls (QualImport "Text.Show.Functions" Nothing : imps ++ ds)
  where
  imps = usort [ QualImport m short | Qualified m short _ <- F.toList d ]

trTheory :: (Ord a,PrettyVar a) => Mode -> Theory a -> Decls (HsId a)
trTheory mode = fixup_prel . trTheory' mode . fmap Other
  where
  fixup_prel =
    case mode of
      Smten -> fmap fx
      _     -> id
    where
    fx (Qualified "Prelude" u v) = Qualified "Smten.Prelude" (Just "S") v
    fx (Qualified "Data.Ratio" u v) = Qualified "Smten.Data.Ratio" (Just "S") v
    fx u = u

data Kind = Expr | Formula deriving Eq

theorySigs :: Theory (HsId a) -> [HsId a]
theorySigs Theory{..} = map sig_name thy_sigs

ufInfo :: Theory (HsId a) -> [H.Type (HsId a)]
ufInfo Theory{thy_sigs} = imps
  where
  imps = [TyImp (Derived f "imp") (H.TyCon (Derived f "") []) | Signature f _ _ <- thy_sigs]

data Mode = Feat | QuickCheck
  | LazySmallCheck
     { with_depth_as_argument  :: Bool
     , with_parallel_functions :: Bool
     }
  | Smten | QuickSpec QuickSpecParams | Plain
  deriving (Eq,Ord,Show)

isLazySmallCheck LazySmallCheck{} = True
isLazySmallCheck _                = False

isSmten Smten{} = True
isSmten _       = False

trTheory' :: forall a b . (a ~ HsId b,Ord b,PrettyVar b) => Mode -> Theory a -> Decls a
trTheory' mode thy@Theory{..} =
  Decls $
    concat [space_decl | isSmten mode ]  ++
    concatMap tr_datatype thy_datatypes ++
    map tr_sort thy_sorts ++
    concatMap tr_sig thy_sigs ++
    concatMap tr_func thy_funcs ++
    tr_asserts thy_asserts ++
    case mode of
      QuickSpec bg -> [makeSig bg thy]
      _ -> []
  where
  imps = ufInfo thy

  space_decl :: [Decl a]
  space_decl =
    [ ClassDecl [] (TyCon (Exact "Space") [TyVar (Exact "stv")])
                      [TySig (Exact "space") []
                         (TyArr (TyCon (prelude "Int") [])
                           (TyCon (smtenSym "Symbolic") [TyVar (Exact "stv")]))
                      ]
    , InstDecl [] (TyCon (Exact "Space") [TyCon (prelude "Bool") []])
        [funDecl
          (Exact "space")
          [d]
          (H.Case (Apply (prelude "<") [var d,H.Int 0])
            [(H.ConPat (prelude "True") [], Apply (smtenMonad "mzero") [])
            ,(H.WildPat,
               Apply (smtenMonad "msum")
                 [List
                   [ Apply (smtenMonad "return") [Apply (prelude "False") []]
                   , Apply (smtenMonad "return") [Apply (prelude "True") []]
                   ]])
            ])
        ]
    ]
    where d = Exact "d"

  tr_datatype :: Datatype a -> [Decl a]
  tr_datatype (Datatype tc _ tvs cons) =
    [ DataDecl tc tvs
        [ (c,map (trType . snd) args) | Constructor c _ _ args <- cons ]
        (map prelude ["Eq","Ord","Show"]
         ++ [typeable "Typeable" | not (isSmten mode) ])
    ]
    ++
    [ TH (Apply (feat "deriveEnumerable") [QuoteTyCon tc])
    | case mode of { Feat -> True; QuickCheck -> True; QuickSpec _ -> True; _ -> False } ]
    ++
    [ InstDecl [H.TyCon (feat "Enumerable") [H.TyVar a] | a <- tvs]
               (H.TyCon (quickCheck "Arbitrary") [H.TyCon tc (map H.TyVar tvs)])
               [funDecl
                  (quickCheck "arbitrary") []
                  (Do [Bind (Exact "k") (Apply (quickCheck "sized") [Apply (prelude "return") []]),
                       Bind (Exact "n") (Apply (quickCheck "choose") [Tup [H.Int 0, Apply (Exact "k") []]])]
                      (Apply (feat "uniform") [Apply (Exact "n") []]))]
    | case mode of { QuickCheck -> True; QuickSpec _ -> True; _ -> False } ]
    ++
    [ InstDecl
        [H.TyCon (lsc "Serial") [H.TyVar a] | a <- tvs]
        (H.TyCon (lsc "Serial") [H.TyCon tc (map H.TyVar tvs)])
        [funDecl
          (lsc "series")
          []
          (foldr1
            (\ e1 e2 -> Apply (lsc "\\/") [e1,e2])
            [ foldl
               (\ e _ -> Apply (lsc "><") [e,Apply (lsc "series") []])
               (Apply (lsc "cons") [Apply c []])
               as
            | Constructor c _ _ as <- cons
            ])]
    | isLazySmallCheck mode ]
    ++
    [ InstDecl
        [H.TyCon (Exact "Space") [H.TyVar a] | a <- tvs]
        (H.TyCon (Exact "Space") [H.TyCon tc (map H.TyVar tvs)])
        [funDecl
          (Exact "space")
          [d]
          (H.Case (Apply (prelude "<") [var d,H.Int 0])
            [(H.ConPat (prelude "True") [], Apply (smtenMonad "mzero") [])
            ,(H.WildPat,
               Apply (smtenMonad "msum")
                 [List
                   [ foldl (\ e1 _ ->
                             Apply (smtenMonad "ap")
                               [e1,Apply (Exact "space")
                                     [Apply (prelude "-") [var d,H.Int 1]]])
                           (Apply (smtenMonad "return") [Apply c []])
                           args
                   | Constructor c _ _ args <- cons
                   ]])
            ])
        ]
    | let d = Exact "d"
    , isSmten mode
    ]

  tr_sort :: Sort a -> Decl a
  tr_sort (Sort s _ i) | null i = TypeDef (TyCon s []) (TyCon (prelude "Int") [])
  tr_sort (Sort _ _ _) = error "Haskell.Translate: Poly-kinded abstract sort"

  tr_sig :: Signature a -> [Decl a]
  tr_sig (Signature f _ pt) =
    -- newtype f_NT = f_Mk (forall tvs . (Arbitrary a, CoArbitrary a) => T)
    [ DataDecl (Derived f "") [] [ (Derived f "Mk",[tr_polyTypeArbitrary pt]) ] []
    , FunDecl (Derived f "get")
       [( [H.ConPat (Derived f "Mk") [VarPat (Derived f "x")]]
        , var (Derived f "x")
        )]

    -- f :: (?f_imp :: f_NT) => T
    -- f = f_get ?f_imp
    , TySig f [] (tr_polyType pt)
    , funDecl f [] (Apply (Derived f "get") [ImpVar (Derived f "imp")])

    -- instance Arbitrary f_NT where
    --   arbitrary = do
    --      Capture x <- capture
    --      return (f_Mk (x arbitrary))
    , InstDecl [] (TyCon (quickCheck "Arbitrary") [TyCon (Derived f "") []])
        [ funDecl (quickCheck "arbitrary") []
          (mkDo [Bind (Derived f "x") (Apply (quickCheckUnsafe "capture") [])]
                (H.Case (var (Derived f "x"))
                   [(H.ConPat (quickCheckUnsafe "Capture") [VarPat (Derived f "y")]
                    ,Apply (prelude "return")
                    [Apply (Derived f "Mk")
                    [Apply (Derived f "y")
                    [Apply (quickCheck "arbitrary") []]]]
                    )]
                )
          )
        ]

    -- gen :: Gen (Dict (?f_imp :: f_NT))
    -- gen = do
    --   x <- arbitrary
    --   let ?f_imp = x
    --   return Dict
    , TySig (Derived f "gen") []
        (TyCon (quickCheck "Gen")
          [TyCon (quickSpec "Dict")
            [TyImp (Derived f "imp") (TyCon (Derived f "") [])]])
    , funDecl (Derived f "gen") []
        (mkDo [Bind (Derived f "x") (Apply (quickCheck "arbitrary") [])]
              (ImpLet (Derived f "imp") (var (Derived f "x"))
                (Apply (prelude "return") [Apply (quickSpec "Dict") []])))
    ]

  tr_func :: Function a -> [Decl a]
  tr_func fn@Function{..} =
    [ TySig func_name [] (tr_polyType (funcType fn))
    , FunDecl
        func_name
        [ (map tr_deepPattern dps,tr_expr Expr rhs)
        | (dps,rhs) <- patternMatchingView func_args func_body
        ]
    ] ++
    [ FunDecl
        (prop_version func_name)
        [ (map tr_deepPattern dps,tr_expr Formula rhs)
        | (dps,rhs) <- patternMatchingView func_args func_body
        ]
    | isLazySmallCheck mode
       && with_parallel_functions mode
       && func_res == boolType
    ]

  prop_version f = Derived f "property"

  tr_asserts :: [T.Formula a] -> [Decl a]
  tr_asserts fms =
    let (info,decls) = unzip (zipWith tr_assert [1..] fms)
    in  concat decls ++
          case mode of
            QuickCheck ->
              [ TH (Apply (prelude "return") [List []])
              , funDecl (Exact "main") []
                  (mkDo [ Stmt (THSplice (Apply (quickCheckAll "polyQuickCheck")
                                                [QuoteName name]))
                        | (name,_) <- info ]
                        Noop)
              ]
            LazySmallCheck{..} ->
              [ funDecl (Exact "main") []
                  ((`mkDo` Noop)
                     $  [Bind (Exact "args") (Apply (sysEnv "getArgs") [])]
                     ++ [Stmt (fn name) | (name,_) <- info])
              ]
              where
              fn name = case with_depth_as_argument of
                         False   -> Apply (lsc "test") [var name]
                         True    -> Apply (lsc "depthCheck")
                                      [read_head (var (Exact "args"))
                                      ,var name]
            Feat ->
              [ funDecl (Exact "main") []
                  (mkDo [Stmt (Apply (feat "featCheckStop")
                          [ H.Lam [TupPat (map VarPat vs)] (Apply name (map var vs))
                          ])
                        | (name,vs) <- info ] Noop)
              ]
            Smten | let [(name,vs)] = info ->
              [ funDecl (Exact "main") []
                  $ mkDo [Bind (Exact "args") (Apply (smtenEnv "getArgs") [])
                         ,Bind (Exact "r")
                          (Apply (smtenSym "run_symbolic")
                            [Apply (smtenMinisat "minisat") []
                            ,mkDo (
                              [ Bind v (Apply (Exact "space") [read_head (var (Exact "args"))])
                              | v <- vs ]
                              ++
                              [ Stmt $ Apply (smtenMonad "guard") [Apply (prelude "not") [Apply name (map var vs)]] ])
                              (Apply (smtenMonad "return") [nestedTup (map var vs)])
                            ])
                        ]
                        (Apply (prelude "print") [var (Exact "r")])
              ]
            _ -> []
    where
    read_head e = Apply (prelude "read") [Apply (prelude "head") [e]]

  tr_assert :: Int -> T.Formula a -> ((a,[a]),[Decl a])
  tr_assert i T.Formula{..} =
    ((prop_name,args),
      [ TySig prop_name []
          (foldr TyArr
             (case mode of LazySmallCheck{} -> H.TyCon (lsc "Property") []
                           _                -> H.TyCon (prelude "Bool") [])
             [ trType (applyType fm_tvs (replicate (length fm_tvs) (intType)) t)
             | Local _ t <- typed_args ])
      | mode == Feat || isLazySmallCheck mode || mode == Smten ]
      ++
      [ funDecl prop_name args (assume (tr_expr (if mode == Feat || isSmten mode then Expr else Formula) body)) ]
    )
    where
    prop_name | i == 1    = Exact "prop"
              | otherwise = Exact ("prop" ++ show i)
    (typed_args,body) =
      case fm_body of
        Quant _ Forall lcls term -> (lcls,term)
        _                        -> ([],fm_body)
    args = map lcl_name typed_args

    assume e =
      case fm_role of
        Prove  -> e
        Assert -> e -- Apply (tipDSL "assume") [e]

  tr_deepPattern :: DeepPattern a -> H.Pat a
  tr_deepPattern (DeepConPat Global{..} dps) = H.ConPat gbl_name (map tr_deepPattern dps)
  tr_deepPattern (DeepVarPat Local{..})      = VarPat lcl_name
  tr_deepPattern (DeepLitPat (T.Int i))      = IntPat i
  tr_deepPattern (DeepLitPat (Bool b))       = withBool H.ConPat b

  tr_pattern :: T.Pattern a -> H.Pat a
  tr_pattern Default = WildPat
  tr_pattern (T.ConPat Global{..} xs) = H.ConPat gbl_name (map (VarPat . lcl_name) xs)
  tr_pattern (T.LitPat (T.Int i))     = H.IntPat i
  tr_pattern (T.LitPat (Bool b))      = withBool H.ConPat b

  tr_expr :: Kind -> T.Expr a -> H.Expr a
  tr_expr k e0 =
    case e0 of
      Builtin (Lit (T.Int i)) :@: [] -> H.Int i
      Builtin (Lit (Bool b)) :@: [] -> lsc_lift (withBool Apply b)
      Builtin Implies :@: [u,v] | mode == Smten -> tr_expr k (Builtin Or :@: [Builtin Not :@: [u],v])
      hd :@: es -> let ((f,k'),lft) = tr_head (map exprType es) k hd
                   in  lift_if lft (maybe_ty_sig e0 (Apply f (map (tr_expr k') es)))
      Lcl x -> lsc_lift (var (lcl_name x))
      T.Lam xs b  -> H.Lam (map (VarPat . lcl_name) xs) (tr_expr Expr b)
      Match e alts -> H.Case (tr_expr Expr e) [ (tr_pattern p,tr_expr brs_k rhs) | T.Case p rhs <- default_last alts ]
        where
        brs_k
          | isLazySmallCheck mode = k
          | otherwise             = Expr
      T.Let x e b -> H.Let (lcl_name x) (tr_expr Expr e) (tr_expr k b)
      T.Quant _ q xs b ->
        foldr
          (\ x e ->
              Apply (tipDSL (case q of Forall -> "forAll"; Exists -> "exists"))
                [H.Lam [VarPat (lcl_name x)] e])
          (tr_expr Formula b)
          xs
      T.LetRec{} -> ERROR("letrec not supported")

    where
    maybe_ty_sig e@(hd@(Gbl Global{..}) :@: es) he
       | isNothing (makeGlobal gbl_name gbl_type (map exprType es) Nothing)
         = he ::: trType (exprType e)
    maybe_ty_sig _ he = he

    lift_if b e
      | b && isLazySmallCheck mode = Apply (lsc "lift") [e]
      | otherwise = e
    lsc_lift = lift_if (k == Formula)

    default_last (def@(T.Case Default _):alts) = alts ++ [def]
    default_last alts = alts

  tr_head :: [T.Type a] -> Kind -> T.Head a -> ((a,Kind),Bool)
  tr_head ts k (Builtin b)      = tr_builtin ts k b
  tr_head ts k (Gbl Global{..})
    | stay_prop = ((prop_version gbl_name,Expr),False)
    | otherwise = ((gbl_name             ,Expr),k == Formula)
    where
    stay_prop = k == Formula
             && isLazySmallCheck mode
             && with_parallel_functions mode
             && polytype_res gbl_type == boolType

  tr_builtin :: [T.Type a] -> Kind -> T.Builtin -> ((a,Kind),Bool)
  tr_builtin ts k b =
    case b of
      At        -> ((prelude "id",Expr),False)
      Lit{}     -> error "tr_builtin"
      And       -> case_kind (tipDSL ".&&.") (Just (lsc "*&*"))
      Or        -> case_kind (tipDSL ".||.") (Just (lsc "*|*"))
      Not       -> case_kind (tipDSL "neg")  (Just (lsc "neg"))
      Implies   -> case_kind (tipDSL "==>")  (Just (lsc "*=>*"))
      Equal     -> case_kind (tipDSL "===") $ case ts of
                                                BuiltinType Boolean:_ -> Just (lsc "*=*")
                                                _                     -> Nothing
      Distinct  -> case_kind (tipDSL "=/=")  Nothing
      _         -> (prelude_fn,False)
    where
    Just prelude_str_ = lookup b hsBuiltins
    prelude_fn = (prelude prelude_str_,Expr)

    case_kind tip_version lsc_version =
      case k of
        Expr    -> (prelude_fn,False)
        Formula ->
          case mode of
            LazySmallCheck{} ->
              case lsc_version of
                Just v  -> ((v,Formula),False)
                Nothing -> (prelude_fn,True)
            _ -> ((tip_version,Formula),False)

  -- ignores the type variables
  tr_polyType_inner :: T.PolyType a -> H.Type a
  tr_polyType_inner (PolyType _ ts t) = trType (ts :=>: t)

  tr_polyType :: T.PolyType a -> H.Type a
  tr_polyType pt@(PolyType tvs _ _) =
    TyForall tvs (TyCtx (arb tvs ++ imps) (tr_polyType_inner pt))

  -- translate type and add Arbitrary a, CoArbitrary a in the context for
  -- all type variables a
  tr_polyTypeArbitrary :: T.PolyType a -> H.Type a
  tr_polyTypeArbitrary pt@(PolyType tvs _ _) = TyForall tvs (TyCtx (arb tvs) (tr_polyType_inner pt))

  arb = arbitrary . map H.TyVar

arbitrary :: [H.Type (HsId a)] -> [H.Type (HsId a)]
arbitrary ts =
  [ TyCon tc [t]
  | t <- ts
  , tc <- [prelude "Ord"]]

      --quickCheck "Arbitrary", feat "Enumerable", prelude "Ord"]

trType :: (a ~ HsId b) => T.Type a -> H.Type a
trType (T.TyVar x)     = H.TyVar x
trType (T.TyCon tc ts) = H.TyCon tc (map trType ts)
trType (ts :=>: t)     = foldr TyArr (trType t) (map trType ts)
trType (BuiltinType b) = trBuiltinType b

trBuiltinType :: BuiltinType -> H.Type (HsId a)
trBuiltinType t
  | Just ty <- lookup t hsBuiltinTys = H.TyCon ty []
  | otherwise = __

withBool :: (a ~ HsId b) => (a -> [c] -> d) -> Bool -> d
withBool k b = k (prelude (show b)) []

-- * Builtins

hsBuiltinTys :: [(T.BuiltinType, HsId a)]
hsBuiltinTys =
  [ (Integer, prelude "Int")
  , (Real,    ratio   "Rational")
  , (Boolean, prelude "Bool")
  ]

hsBuiltins :: [(T.Builtin,String)]
hsBuiltins =
  [ (Equal    , "==" )
  , (Distinct , "/=" )
  , (NumAdd   , "+"  )
  , (NumSub   , "-"  )
  , (NumMul   , "*"  )
  , (NumDiv   , "/"  )
  , (IntDiv   , "div")
  , (IntMod   , "mod")
  , (NumGt    , ">"  )
  , (NumGe    , ">=" )
  , (NumLt    , "<"  )
  , (NumLe    , "<=" )
  , (NumWiden , "fromIntegral")
  , (And      , "&&" )
  , (Or       , "||" )
  , (Not      , "not")
  , (Implies  , "<=" )
  ]

typesOfBuiltin :: Builtin -> [T.Type a]
typesOfBuiltin b = case b of
  And      -> [bbb]
  Or       -> [bbb]
  Not      -> [bb]
  Implies  -> [bbb]
  Equal    -> [iib] -- TODO: equality could be used on other types than int
  Distinct -> [iib] -- ditto
  NumAdd   -> [iii, rrr]
  NumSub   -> [iii, rrr]
  NumMul   -> [iii, rrr]
  NumDiv   -> [rrr]
  IntDiv   -> [iii]
  IntMod   -> [iii, rrr]
  NumGt    -> [iib, rrb]
  NumGe    -> [iib, rrb]
  NumLt    -> [iib, rrb]
  NumLe    -> [iib, rrb]
  NumWiden -> [ir]
  _        -> __
  where
  bb  = [boolType] :=>: boolType
  bbb = [boolType,boolType] :=>: boolType
  iii = [intType,intType] :=>: intType
  iib = [intType,intType] :=>: boolType
  rrr = [realType,realType] :=>: realType
  rrb = [realType,realType] :=>: boolType
  ir  = [intType] :=>: realType

-- * QuickSpec signatures

data QuickSpecParams =
  QuickSpecParams {
    background_functions :: [String],
    exploration_type :: [String], -- type that needs observer
    observation_type :: [String], -- observable type
    observation_fun :: [String] -- corresponding observation function
    }
  deriving (Eq, Ord, Show)

makeSig :: forall a . (PrettyVar a,Ord a) => QuickSpecParams -> Theory (HsId a) -> Decl (HsId a)
makeSig QuickSpecParams{..} thy@Theory{..} =
  funDecl (Exact "sig") [] $
    Tup
      [ List
          [ Tup
              [ constant_decl (varStr (fst ft) `elem` background_functions) ft
              , List $
                  if use_cg
                    then
                      [ int_lit num
                      | (members,num) <- cg `zip` [0..]
                      , f `elem` members
                      ]
                    else
                      [int_lit 0]

              ]
          | ft@(f,_) <- func_constants
          ]
      , Apply (quickSpec "signature") [] `Record`
          [ (quickSpec "constants",
               List $
                 builtin_decls ++
                 map (constant_decl True)
                   (ctor_constants ++ builtin_constants))
          , (quickSpec "instances", List $
               map instance_decl (ctor_constants ++ builtin_constants ++ func_constants) ++
               [ Apply (quickSpec "baseType") [Apply (prelude "undefined") [] ::: H.TyCon (ratio "Rational") []] ] ++
               [ mk_inst [] (mk_class (feat "Enumerable") (H.TyCon (prelude "Int") [])) ] ++
               [ mk_inst (map (mk_class c1) tys) (mk_class c2 (H.TyCon t tys))
               | (t,n) <- type_univ
               , (c1, c2) <- [(prelude "Ord", prelude "Ord")--,
                              --(feat "Enumerable", feat "Enumerable"),
                              --(feat "Enumerable",quickCheck "Arbitrary")
                             ]
               , let tys = map trType (qsTvs n)
               ] ++
               [ Apply (quickSpec "makeInstance") [H.Lam [TupPat []] (Apply (Derived f "gen") [])]
               | Signature f _ _ <- thy_sigs
               ] ++ obs_decl
            )
          , (quickSpec "maxTermSize", Apply (prelude "Just") [H.Int 7])
          , (quickSpec "maxTermDepth", Apply (prelude "Just") [H.Int 4])
          , (quickSpec "testTimeout", Apply (prelude "Just") [H.Int 100000])
          ]
      ]
  where
  imps = ufInfo thy

  use_cg = True

  int_lit x = H.Int x ::: H.TyCon (prelude "Int") []

  mk_inst ctx res =
    Apply (quickSpec ("inst" ++ concat [ show (length ctx) | length ctx >= 2 ]))
                 [ Apply (quickSpec "Sub") [Apply (quickSpec "Dict") []] :::
                   H.TyCon (quickSpec ":-") [TyTup ctx,res] ]

  mk_class c x = H.TyCon c [x]

  scp = scope thy

  cg = map (map defines) (flatCallGraph (CallGraphOpts False False) thy)

  poly_type (PolyType _ args res) = args :=>: res

  constant_decl background (f,t) =
    Record (Apply (quickSpec "constant") [H.String f,lam (Apply f []) ::: qs_type]) $
      [(quickSpec "conSize", H.Int 0)] ++
      [(quickSpec "conIsBackground", H.Apply (prelude "True") []) | background]

    where
    (_pre,qs_type) = qsType t
    lam = H.Lam [H.ConPat (quickSpec "Dict") []]

  instance_decl (_,t) =
    Apply (quickSpec "makeInstance") [H.Lam [foldr pairPat (H.TupPat []) args] res ::: ty]
    where
      (pre, _) = qsType t
      args = replicate (length pre) (H.ConPat (quickSpec "Dict") [])
      res  = H.Apply (prelude "return") [H.Apply (quickSpec "Dict") []]

      ty = TyArr (foldr tyPair (H.TyTup []) (map dict pre)) (TyCon (quickCheck "Gen") [dict (TyTup pre)])
      dict x = TyCon (quickSpec "Dict") [x]

      pairPat x y = H.TupPat [x,y]
      tyPair x y = H.TyTup [x,y]

  obs_decl
    | length (exploration_type ++ observation_type ++ observation_fun) < 3 = []
    | otherwise = [Apply (quickSpec "makeInstance") [H.Lam [H.ConPat (quickSpec "Dict") []]
                            (Apply (quickSpec "observe") [obs]) :::
                  H.TyArr d (H.TyCon (quickSpec "Observe") [H.TyCon t [x], H.TyCon t' [x]]) ]]
    where
      d = H.TyCon (quickSpec "Dict") [H.TyCon (prelude "Ord") [x]]
      --[H.TyTup [H.TyCon (prelude "Ord") [x], H.TyCon (feat "Enumerable") [x], H.TyCon (quickCheck "Arbitrary") [x]]]
      x = H.TyCon (quickSpec "A") []
      obs = Apply (Qualified "Tip.Haskell.Observers" Nothing "mkObserve") [Apply ofun []]
      ofun = head obsFun
      t = head explType
      t' = head obsType
      explType = filter (\t -> (varStr t == head exploration_type)) (map fst type_univ)
      obsType = filter (\t -> (varStr t == head observation_type)) (map fst type_univ)
      obsFun = filter (\f -> (varStr f == head observation_fun)) (map fst func_constants)

  int_lit_decl x =
    Record (Apply (quickSpec "constant") [H.String (Exact (show x)),int_lit x])
      [(quickSpec "conIsBackground", H.Apply (prelude "True") [])]

  bool_lit_decl b =
    Record (Apply (quickSpec "constant") [H.String (prelude (show b)),withBool Apply b])
      [(quickSpec "conIsBackground", H.Apply (prelude "True") [])]

  ctor_constants =
    [ (f,poly_type (globalType g))
    | (f,g@ConstructorInfo{}) <- M.toList (globals scp)
    ]

  func_constants =
    [ (f,poly_type (globalType g))
    | (f,g@FunctionInfo{}) <- M.toList (globals scp)
    ]

  type_univ =
    [ (data_name, length data_tvs)
    | (_,DatatypeInfo Datatype{..}) <- M.toList (types scp)
    ]

  -- builtins

  (builtin_lits,builtin_funs) =
    partition (litBuiltin . fst) $
      usort
        [ (b, map exprType args :=>: exprType e)
        | e@(Builtin b :@: args) <- universeBi thy ]

  used_builtin_types :: [BuiltinType]
  used_builtin_types =
    usort [ t | BuiltinType t :: T.Type (HsId a) <- universeBi thy ]

  bool_used = Boolean `elem` used_builtin_types
  num_used  = -- Integer `elem` used_builtin_types
              or [ op `elem` map fst builtin_funs | op <- [NumAdd,NumSub,NumMul,NumDiv,IntDiv,IntMod] ]

  builtin_decls
    =  [ bool_lit_decl b | bool_used, b <- [False,True] ]
    ++ [ int_lit_decl x  | num_used,  x <- nub $
                                           [0,1] ++
                                           [ x
                                           | Lit (T.Int x) <- map fst builtin_lits ]]

  builtin_constants
    =  [ (prelude s, ty)
       | (b, ty) <- nub $
           -- [ b      | bool_used, b <- [And,Or,Not] ]
           -- [ IntAdd | int_used ]
           -- [ Equal  | bool_used && int_used ]
              [ (b, ty) | (b, ty) <- builtin_funs, numBuiltin b ]
       , Just s <- [lookup b hsBuiltins]
       ]

  qsType :: Ord a => T.Type (HsId a) -> ([H.Type (HsId a)],H.Type (HsId a))
  qsType t = (pre, TyArr (TyCon (quickSpec "Dict") [TyTup pre]) inner)
    where
    pre = arbitrary (map trType qtvs) ++ imps
    inner = trType (applyType tvs qtvs t)
    qtvs = qsTvs (length tvs)
    tvs = tyVars t

  qsTvs :: Int -> [T.Type (HsId a)]
  qsTvs n = take n (cycle [ T.TyCon (quickSpec qs_tv) [] | qs_tv <- ["A","B","C","D","E"] ])

theoryBuiltins :: Ord a => Theory a -> [T.Builtin]
theoryBuiltins = usort . universeBi

