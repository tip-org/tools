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

import Data.Maybe (isNothing, catMaybes, listToMaybe)

import Tip.CallGraph

import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import qualified Data.Map as M

import Data.Generics.Geniplate

import Data.List (nub,partition,find)

import qualified GHC.Generics as G

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

quickSpecInternal :: String -> HsId a
quickSpecInternal = Qualified "QuickSpec.Internal" (Just "QS")

constraints :: String -> HsId a
constraints = Qualified "Data.Constraint" (Just "QS")

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

generic :: String -> HsId a
generic = Qualified "GHC.Generics" (Just "G")

genericArbitrary :: String -> HsId a
genericArbitrary = Qualified "Tip.Haskell.GenericArbitrary" (Just "GA")

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
    Decls (map LANGUAGE ["TemplateHaskell","DeriveDataTypeable","TypeOperators",
                         "ImplicitParams","RankNTypes","DeriveGeneric", "MultiParamTypeClasses"]
            ++ Module mod_name : ds)

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
    map tr_sort thy_sorts ++
    concatMap tr_datatype thy_datatypes ++
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
  tr_datatype dt@(Datatype tc _ tvs cons) =
    [ DataDecl tc tvs
        [ (c,map (trType . snd) args) | Constructor c _ _ args <- cons ]
        (map prelude ["Eq","Ord","Show"]
         ++ [generic "Generic"]
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
                  (Do [Bind (Exact "k") (Apply (quickCheck "sized")
                                         [Apply (prelude "return") []]),
                       Bind (Exact "n") (Apply (quickCheck "choose")
                                         [Tup [H.Int 0, Apply (prelude "+") [Apply (prelude "*") [Apply (Exact "k") [], H.Int 2], H.Int 2]]])]
                      (Apply (feat "uniform") [Apply (Exact "n") []]))]
    | case mode of { QuickCheck -> True; QuickSpec QuickSpecParams{..} -> not use_observers;
                     _ -> False } ]
    ++
    [ InstDecl [H.TyTup ([H.TyCon (typeable "Typeable") [H.TyVar a] | a <- tvs]
                         ++ [H.TyCon (quickCheck "Arbitrary") [H.TyVar a] | a <- tvs])]
               (H.TyCon (quickCheck "Arbitrary") [H.TyCon tc (map H.TyVar tvs)])
               [funDecl
                  (quickCheck "arbitrary") []
                  (Apply (genericArbitrary "genericArbitrary") [])]
    | case mode of { QuickSpec QuickSpecParams{..} -> use_observers; _ -> False } ]
    ++
    [ InstDecl [H.TyCon (quickCheck cls) [H.TyVar a] | a <- tvs, cls <- ["Arbitrary", "CoArbitrary"]]
               (H.TyCon (quickCheck "CoArbitrary") [H.TyCon tc (map H.TyVar tvs)])
               [funDecl
               (quickCheck "coarbitrary") []
               (Apply (quickCheck "genericCoarbitrary") [])]]
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
    ++ (obsType dt)
    where
      obsType :: Datatype a -> [Decl a]
      obsType dt@(Datatype tc _ tvs cons) =
        case mode of QuickSpec QuickSpecParams{..} ->
                       if use_observers then
                         [DataDecl (obsName tc) tvs
                           ([ (obsName c, map (trObsType . snd) args)
                            | Constructor c _ _ args <- cons ]
                            ++
                            [(nullConsName tc,[])]
                           )
                           (map prelude ["Eq","Ord","Show"]
                             ++ [typeable "Typeable"])
                         ]
                         ++ (obsFun dt [] (obFuName (data_name dt))
                             (obFuType (data_name dt) (data_tvs dt)) False)
                         ++ (nestedObsFuns thy dt)
                         ++ [InstDecl [H.TyCon (prelude "Ord") [H.TyVar a] | a <- tvs]
                              (H.TyCon (quickSpec "Observe") $
                                 [H.TyCon (genericArbitrary "Scaled") []]
                              ++ [H.TyCon (obsName tc) (map H.TyVar tvs)]
                              ++ [H.TyCon tc (map H.TyVar tvs)]
                              )
                              [funDecl (quickSpec "observe") [Exact "s"]
                                       (Apply (obFuName tc) [Apply (genericArbitrary "scaled") [H.Int (fromIntegral max_observer_size), var (Exact "s")]])
                              ]
                            ]
                       else []
                     _ -> []

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
          [TyCon (constraints "Dict")
            [TyImp (Derived f "imp") (TyCon (Derived f "") [])]])
    , funDecl (Derived f "gen") []
        (mkDo [Bind (Derived f "x") (Apply (quickCheck "arbitrary") [])]
              (ImpLet (Derived f "imp") (var (Derived f "x"))
                (Apply (prelude "return") [Apply (constraints "Dict") []])))
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

  arb = (arbitrary ob) . map H.TyVar
  ob = case mode of
    QuickSpec QuickSpecParams{..} -> use_observers
    _ -> False

arbitrary :: Bool -> [H.Type (HsId a)] -> [H.Type (HsId a)]
arbitrary obs ts =
  [ TyCon tc [t]
  | t <- ts
  , tc <- tcs]
  where tcs = case obs of
          True -> []--quickCheck "Arbitrary", quickCheck "CoArbitrary", typeable "Typeable"]
          False -> [quickCheck "Arbitrary", feat "Enumerable", prelude "Ord"]

trType :: (a ~ HsId b) => T.Type a -> H.Type a
trType (T.TyVar x)     = H.TyVar x
trType (T.TyCon tc ts) = H.TyCon tc (map trType ts)
trType (ts :=>: t)     = foldr TyArr (trType t) (map trType ts)
trType (BuiltinType b) = trBuiltinType b

trObsType :: (a ~ HsId b) => T.Type a -> H.Type a
trObsType (T.TyCon tc ts) = H.TyCon (obsName tc) (map trObsType ts)
trObsType t                = trType t

-- Name of generated observer type
-- obsName T_name = ObsT_name
obsName :: HsId a -> HsId a
obsName c = Derived c "Obs"

-- Name of nullary constructor for generated observer type
-- nullConsName T_name = NullConsT_name
nullConsName :: HsId a -> HsId a
nullConsName c = Derived c "NullCons"

-- Name of generated observer function
-- obFuName T_name = obsFunT_name
obFuName :: PrettyVar a => HsId a -> HsId a
obFuName c = Exact $ "obsFun" ++ varStr c

-- Type of generated observer function
obFuType :: (a ~ HsId b) => a -> [a] -> H.Type a
obFuType c vs =
  -- Int -> dt -> obs_dt
  TyArr (TyVar $ prelude "Int") (TyArr (TyCon c (map (\x -> TyVar x) vs))
                                     (TyCon (obsName c) (map (\x -> TyVar x) vs)))

-- Name of recursive observer for nested type
nestObsName :: (a ~ HsId b, PrettyVar b) => T.Type a -> HsId b
nestObsName (T.TyCon tc ts) = Exact $ foldl (++) ("obsFun" ++ varStr tc) (map nestName ts)
  where nestName (T.TyCon c s) = (foldr (++) (varStr c) (map nestName s))
        nestName _             = ""
nestObsName _               = Exact ""

-- Type of recursive observer for nested type
nestObsType :: (a ~ HsId b) => T.Type a -> H.Type a
nestObsType t = TyArr (TyVar $ prelude "Int") (TyArr (trType t) (trObsType t))

-- observer functions for nested constructors
nestedObsFuns :: (a ~ HsId b, Eq b, PrettyVar b) => Theory a -> Datatype a -> [Decl a]
nestedObsFuns thy dt@(Datatype tc _ tvs cons) = concat $ catMaybes $ concatMap (nestedObs thy) cons

-- generate observers if constructor is nested
nestedObs :: (a ~ HsId b, Eq b, PrettyVar b) => Theory a -> Constructor a -> [Maybe [Decl a]]
nestedObs thy (Constructor _ _ _ as) = map ((nestObs thy) . snd) as

-- generate observer if constructor is found nested inside another constructor
nestObs :: (a ~ HsId b, Eq b, PrettyVar b) => Theory a -> T.Type a -> Maybe [Decl a]
nestObs Theory{..} t@(T.TyCon tc ts) = case find (\x -> (data_name x == tc)) thy_datatypes of
  Just dt ->
    if nestObsName t == obFuName tc
    then Nothing
    else Just $ obsFun dt ts (nestObsName t) (nestObsType t) True
  _       -> Nothing
nestObs _ _ = Nothing

-- Generate observer function for the given type
obsFun :: (a ~ HsId b, Eq b, PrettyVar b) => Datatype a -> [T.Type a] -> a -> H.Type a -> Bool -> [Decl a]
obsFun (Datatype tname _ _ cons) targs fuName fuType recu =
  [TySig fuName [] fuType, FunDecl fuName cases]
  where
    cases = [
      -- if counter is down to 0 call nullary constructor on rhs
      ([H.VarPat (Exact "0"),
        H.VarPat (Exact "_")], Apply (nullConsName tname) [])
      ,([H.VarPat n, H.VarPat x],
        H.Case (Apply (prelude "<") [var n, H.Int 0])
        -- if n is negative use -n instead
        [(H.ConPat (prelude "True") [],
           Apply fuName [Apply (prelude "negate") [var n], var x])
        -- if n is positive call approx
        ,(H.ConPat (prelude "False") [],
           H.Case (var x) $
           [(H.ConPat cname $ varNames cargs,
             approx recu cname (map snd cargs) (listToMaybe targs) fuName tname)
           | Constructor cname _ _ cargs <- cons]
         )
        ])]
    n = Exact "n"
    x = Exact "x"
    varNames as = map (\((c,a),b) -> mkVar b a) (zip as [0..])
    mkVar n (T.TyVar _)   = H.VarPat (Exact $ "x" ++ (show n))
    mkVar n (T.TyCon tc ts)  = H.ConPat (Exact $ "x" ++ (show n)) []
    mkVar n (BuiltinType b)
      | Just ty <- lookup b hsBuiltinTys = H.ConPat (Exact $ "x" ++ (show n)) []
      | otherwise = __
    mkVar _ _ = WildPat

approx :: (a ~ HsId b, Eq b, PrettyVar b) => Bool -> a -> [T.Type a] -> Maybe (T.Type a) -> a -> a -> H.Expr a
approx recu c as ta fn nm | recu         = Apply (obsName c) $ map (recappstep as ta fn nm) (zip as [0..])
                          | otherwise    = Apply (obsName c) $ map (appstep as nm) (zip as [0..])
  where
    -- regular case
    appstep as nm (t@(T.TyCon _ _), k) =
      -- call the appropriate observer function with decremented counter
      Apply (nestObsName t) [decrement $ countBranches as nm
                            , varName k]
    appstep _ _ (_, k) = varName k
    -- recursive approximation for nested constructors
    recappstep as _ fn nm (t@(T.TyCon _ _), k) =
      -- call the current observer function with decremented counter
      Apply fn $ [decrement $ countBranches as nm
                 , varName k]
    recappstep as (Just ta) fn nm (t@(T.TyVar x), k) =
      -- call recursive observer for nested constructor
      Apply (nestObsName ta) $ [decrement $ countBranches as nm
                               ,varName k]
    recappstep _ _ _  _ (_,k) = varName k
    varName k = var (Exact $ "x" ++ (show k))

-- decrement fuel counter based on branching factor
decrement :: (a ~ HsId b) => Int -> H.Expr a
decrement k =
  if k <= 1
  then
    Apply (prelude "-") [var n, H.Int 1]
  else
    Apply (prelude "quot") [var n, H.Int $ toInteger k]
  where
    n = Exact "n"

-- calculate branching factor
countBranches :: [T.Type a] -> a -> Int
countBranches as n =
  foldr (+) 0 (map bcount as)
  where
    bcount (T.TyCon tc ts) = foldr (+) (isBranch tc) (map bcount ts)
    bcount _ = 0
    isBranch n = 1
    isBranch _ = 0

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
  Lit (T.Int _) -> [intType]
  Lit (Bool _) -> [boolType]
  _        -> error ("can't translate built-in: " ++ show b)
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
    foreground_functions :: Maybe [String],
    predicates :: Maybe [String],
    use_observers :: Bool,
    use_completion :: Bool,
    max_size :: Int,
    max_depth :: Int,
    max_test_size :: Int,
    max_observer_size :: Int
    }
  deriving (Eq, Ord, Show)

makeSig :: forall a . (PrettyVar a, Ord a) => QuickSpecParams -> Theory (HsId a) -> Decl (HsId a)
makeSig qspms@QuickSpecParams{..} thy@Theory{..} =
  funDecl (Exact "sig") [] $ List $
  [constant_decl ft
  | ft@(f,_) <- func_constants, inForeground f] ++
  bg
  ++
  [ mk_inst [] (mk_class (feat "Enumerable") (H.TyCon (prelude "Int") [])) ] ++
  [ mk_inst [] (mk_class (feat "Enumerable") (H.TyCon (prelude "Rational") [])) ] ++
  [ mk_inst [] (mk_class (feat "Enumerable") (H.TyCon (prelude "Bool") [])) ] ++
  [ mk_inst [] (mk_class (quickCheck "Arbitrary") (H.TyCon (prelude "Int") [])) ] ++
  [ mk_inst [] (mk_class (quickCheck "Arbitrary") (H.TyCon (prelude "Rational") [])) ] ++
  [ mk_inst [] (mk_class (quickCheck "Arbitrary") (H.TyCon (prelude "Bool") [])) ] ++
  [ mk_inst [] (mk_class (typeable "Typeable") (H.TyCon (prelude "Int") [])) ] ++
  [ mk_inst [] (mk_class (quickCheck "CoArbitrary") (H.TyCon (prelude "Int") [])) ] ++
  [ mk_inst [] (mk_class (quickCheck "CoArbitrary") (H.TyCon (prelude "Rational") [])) ] ++
  [ mk_inst [] (mk_class (quickCheck "CoArbitrary") (H.TyCon (prelude "Bool") [])) ] ++
  [ mk_inst (map (mk_class c1) tys) (mk_class c2 (H.TyCon t tys))
  | (t,n) <- type_univ
  , (c1, c2) <- [(prelude "Ord", prelude "Ord"),
                  (feat "Enumerable", feat "Enumerable")]
  , let tys = map trType (qsTvs n)
  ] ++
  [ mk_inst [mk_class c ty | c <- cs, ty <- tys] (mk_class c2 (H.TyCon t tys))
  | (t,n) <- type_univ
  , (cs,c2) <- [([quickCheck "Arbitrary", quickCheck "CoArbitrary"],quickCheck "CoArbitrary"),
                ([typeable "Typeable"], typeable "Typeable")]
  , let tys = map trType (qsTvs n)
  ] ++
  [ mk_inst (map (mk_class (feat "Enumerable")) tys)
    (mk_class (quickCheck "Arbitrary") (H.TyCon t tys))
  | (t,n) <- type_univ, t `notElem` (map (\(a,b,c) -> a) obsTriples)
  , let tys = map trType (qsTvs n)
  ] ++
  [ mk_inst ((map (mk_class (typeable "Typeable")) tys)
              ++ (map (mk_class (quickCheck "Arbitrary")) tys)
            ) (mk_class (quickCheck "Arbitrary") (H.TyCon t tys))
  | (t,n) <- type_univ, t `elem` (map (\(a,b,c) -> a) obsTriples)
  , let tys = map trType (qsTvs n)
  ] ++
  [ mk_inst ((map (mk_class (prelude "Ord")) tys)
              ++ (map (mk_class (quickCheck "Arbitrary")) tys)
            ) (H.TyCon (quickSpec "Observe") $
               [H.TyCon (genericArbitrary "Scaled") []]
               ++ [H.TyCon (obsName t) tys]
               ++ [H.TyCon t tys])
  | (t,n) <- type_univ, t `elem` (map (\(a,b,c) -> a) obsTriples)
  , let tys = map trType (qsTvs n)
  ] ++
  [ Apply (quickSpecInternal "instFun") [H.Lam [TupPat []] (Apply (Derived f "gen") [])]
  | Signature f _ _ <- thy_sigs
  ] ++
  [Apply (quickSpec "withMaxTermSize") [H.Int (fromIntegral max_size)]] ++
  [Apply (quickSpec "withMaxTermDepth") [H.Int (fromIntegral max_depth)]] ++
  [Apply (quickSpec "withMaxTestSize") [H.Int (fromIntegral max_test_size)]] ++
  [Apply (quickSpec "withPruningDepth") [H.Int 0] | not use_completion]
  --TODO: What is reasonable size? Make size tweakable?
  --TODO: Set more parameters?
  where
    inForeground f =
      case foreground_functions of
        Nothing -> True
        Just fs -> varStr f `elem` fs
    inPredicates p =
      case predicates of
        Nothing -> True
        Just ps -> varStr p `elem` ps
    bg = case bgs of
      [] -> []
      _ -> [Apply (quickSpec "background") [List bgs]]
    bgs = [constant_decl ft
          | ft@(f,_) <- func_constants,
            not (inForeground f) ]
          ++ builtin_decls
          ++ map constant_decl (ctor_constants ++ builtin_constants)
    imps = ufInfo thy

    int_lit x = H.Int x ::: H.TyCon (prelude "Int") []

    mk_inst ctx res =
      Apply (quickSpec "inst")
                  [ Apply (constraints "Sub") [Apply (constraints "Dict") []] :::
                    H.TyCon (constraints ":-") [TyTup ctx,res] ]

    mk_class c x = H.TyCon c [x]

    scp = scope thy

    poly_type (PolyType _ args res) = args :=>: res

    constant_decl (f,t) =
      -- FIXME: If there are more than 6 constraints quickspec won't find properties
      -- for this function, can we get around that by changing the representation here?
      Apply (quickSpec conOrPred) [H.String f,lam (Apply f []) ::: qs_type]
      where
        (_pre,qs_type) = qsType t
        lam = H.Lam [H.ConPat (constraints "Dict") []]
        conOrPred =
          case t of
            _ :=>: BuiltinType Boolean | inPredicates f -> "predicate"
            _ -> "con"

    int_lit_decl x =
      Apply (quickSpec "con") [H.String (Exact (show x)),int_lit x]

    bool_lit_decl b =
      Apply (quickSpec "con") [H.String (prelude (show b)),withBool Apply b]

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

    -- Types that require observers along with corresponding observer types
    -- and functions
    obsTriples =
      [(data_name, obsName data_name, obFuName data_name)
      | (_,DatatypeInfo dt@Datatype{..}) <- M.toList (types scp),
        use_observers
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
    qsType t = (pre, TyArr (TyCon (constraints "Dict") [tyTup pre]) inner)
    -- FIXME: can we curry the constraints so we don't get tuples of more than 6?
      where
        pre = arbitrary use_observers (map trType qtvs) ++ imps
        -- put each of qtvs in separate Dict?
        inner = trType (applyType tvs qtvs t)
        qtvs = qsTvs (length tvs)
        tvs = tyVars t
        -- Transform big tuples of constraints into nested tuples
        -- (because QuickSpec doesn't understand arbitrary tuples of constraints)
        tyTup [] = TyTup []
        tyTup [ty] = ty
        tyTup (ty:tys) = TyTup [ty, tyTup tys]

    qsTvs :: Int -> [T.Type (HsId a)]
    qsTvs n = take n (cycle [ T.TyCon (quickSpec qs_tv) [] | qs_tv <- ["A","B","C","D","E"] ])

    theoryBuiltins :: Ord a => Theory a -> [T.Builtin]
    theoryBuiltins = usort . universeBi
