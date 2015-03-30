{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards,StandaloneDeriving #-}
module Tip.Id where

import Tip.Pretty
import Text.PrettyPrint (text)

import Name hiding (varName)
import OccName (occNameString)
-- import BasicTypes (TupleSort(..))
import PrelNames
import Tip.GHCUtils
import Var (Var,varName,idDetails,TyVar,tyVarName)
import IdInfo (IdDetails(..))
import TyCon (tyConName,TyCon)
import DataCon (dataConName,DataCon)
import Data.Char (toUpper)

#ifdef SUPPORT_JSON
import Data.Aeson
#endif
import GHC.Generics
import PrimOp

import Data.Map (Map)
import qualified Data.Map as M

import TysWiredIn (trueDataCon,falseDataCon,boolTyCon)

idFromPrimOp :: PrimOp -> Id
idFromPrimOp = GHCPrim

idFromName :: Name -> Id
idFromName nm
    | Just op <- M.lookup (nameOccName nm) primops = idFromPrimOp op
    | otherwise = GHCOrigin nm Nothing Nothing

primops :: Map OccName PrimOp
primops = M.fromList [(primOpOcc o,o) | o <- allThePrimOps]

idFromDataCon :: DataCon -> Id
idFromDataCon = idFromName . dataConName

idFromVar :: Var -> Id
idFromVar i = case idDetails i of
    DataConWorkId dc -> idFromDataCon dc
    DataConWrapId dc -> idFromDataCon dc
    _                -> idFromName (varName i) `withVar` i

idFromTyVar :: TyVar -> Id
idFromTyVar = idFromName . tyVarName

idFromTyCon :: TyCon -> Id
idFromTyCon tc = idFromName (tyConName tc) `withTyCon` tc

tryGetGHCName :: Id -> Maybe Name
tryGetGHCName (GHCOrigin nm _ _) = Just nm
tryGetGHCName _                  = Nothing

GHCOrigin nm _ _ `withVar` v = GHCOrigin nm (Just v) Nothing
i                `withVar` _ = i

GHCOrigin nm _ _ `withTyCon` tc = GHCOrigin nm Nothing (Just tc)
i                `withTyCon` _ = i

tryGetGHCVar :: Id -> Maybe Var
tryGetGHCVar (GHCOrigin _ mv _) = mv
tryGetGHCVar _                  = Nothing

tryGetGHCTyCon :: Id -> Maybe TyCon
tryGetGHCTyCon (GHCOrigin _ _ mtc) = mtc
tryGetGHCTyCon _                   = Nothing

data Id
    = GHCOrigin Name (Maybe Var)   -- The Var is there to look at the call graph
                     (Maybe TyCon) -- There might come more tycons from the signature
    | GHCPrim PrimOp
    | Eta Int
    | Discrim Id
    | Project Id Int
    {-
    | OtherPrim OtherPrim
    | Derived Derived Integer
    | Const Int Int
    | FromProverBool
    | ProverBool
    -}
  deriving (Eq,Ord)

instance Show Id where
    show (GHCOrigin n _ _) = show (showOutputable n)
    show (GHCPrim po)      = "PrimOp"
    show (Eta n)           = "eta" ++ show n
    show (Discrim c)       = "is-" ++ show c
    show (Project c i)     = show c ++ "_" ++ show i

instance Pretty Id where
    pp = text . ppId

ppId :: Id -> String
ppId (GHCOrigin nm _ _) = ppName nm
ppId (GHCPrim po)       = "PrimOp"
ppId (Eta n)            = "eta" ++ show n
ppId (Discrim c)        = "is-" ++ show c
ppId (Project c i)      = case (i,ppId c) of
                            (0,"Cons") -> "head"
                            (1,"Cons") -> "tail"
                            (0,"S")    -> "p"
                            (0,"Succ") -> "pred"
                            _          -> ppId c ++ "_" ++ show i

ppName :: Name -> String
ppName nm
    | k == listTyConKey      = "List"
    | k == nilDataConKey     = "Nil"
    | k == consDataConKey    = "Cons"
    | k == unitTyConKey      = "UnitTyCon"
    | k == genUnitDataConKey = "Unit"
    | otherwise = case getOccString nm of
        "(,)"  -> "Tup"
        "(,,)" -> "Trip"
        "+"   -> "plus"
        "-"   -> "minus"
        "/"   -> "div"
        "*"   -> "mult"
        "^"   -> "pow"
        "++"  -> "append"
        ">>=" -> "bind"
        "=<<" -> "dnib"
        ">=>" -> "dot_monadic"
        "<=<" -> "monadic_dot"
        "<*>" -> "ap"
        "<$>" -> "fmap"
        ">>"  -> "then"
        "||"  -> "or"
        "&&"  -> "and"
        "."   -> "dot"
        "=="  -> "equal"
        "/="  -> "unequal"
        ">"   -> "gt"
        ">="  -> "ge"
        "<"   -> "lt"
        "<="  -> "le"
        "$"   -> "apply"
        "!!"  -> "index"
        "\\\\" -> "difference"
        s     -> s
  where
    k = getUnique nm

{-
data OtherPrim
    = IntGt
    | IntGe
    | IntEq
    | IntNe
    | IntLt
    | IntLe
    | ProverTrue
    | ProverFalse
  deriving (Eq,Ord,Show,Generic,Enum,Bounded)

convertIntegerToInt :: Name -> Maybe PrimOp
convertIntegerToInt x = case () of
    () | u == plusIntegerIdKey   -> Just IntAddOp
       | u == timesIntegerIdKey  -> Just IntMulOp
       | u == minusIntegerIdKey  -> Just IntSubOp
       | u == eqIntegerPrimIdKey -> Just IntEqOp
       | u == neqIntegerPrimIdKey -> Just IntNeOp
       | u == geIntegerPrimIdKey -> Just IntGeOp
       | u == gtIntegerPrimIdKey -> Just IntGtOp
       | u == leIntegerPrimIdKey -> Just IntLeOp
       | u == ltIntegerPrimIdKey -> Just IntLtOp
{-
       | u == divIntegerIdKey    -> error "Use quot instead of div"
       | u == modIntegerIdKey    -> error "Use rem instead of mod"
       | u == remIntegerIdKey    -> Just IntRemOp
       | u == quotIntegerIdKey   -> Just IntQuotOp
-}
       | otherwise               -> Nothing
  where
    u = nameUnique x

convertPrim :: PrimOp -> Maybe OtherPrim
convertPrim op = case op of
    IntGtOp -> Just IntGt
    IntGeOp -> Just IntGe
    IntEqOp -> Just IntEq
    IntNeOp -> Just IntNe
    IntLtOp -> Just IntLt
    IntLeOp -> Just IntLe

    CharGtOp -> Just IntGt
    CharGeOp -> Just IntGe
    CharEqOp -> Just IntEq
    CharNeOp -> Just IntNe
    CharLtOp -> Just IntLt
    CharLeOp -> Just IntLe
    _       -> Nothing

otherPrims :: [OtherPrim]
otherPrims = [minBound..maxBound]

ghcBool :: Id
ghcBool = idFromTyCon boolTyCon

ghcTrue, ghcFalse :: Id
ghcTrue  = idFromDataCon trueDataCon
ghcFalse = idFromDataCon falseDataCon

proverBool :: Id
proverBool = ProverBool

proverTrue,proverFalse :: Id
proverTrue  = OtherPrim ProverTrue
proverFalse = OtherPrim ProverFalse

instance Show Name where
    show nm = show (showOutputable nm)

instance Show Var where
    show _ = "<Var>"

instance Show TyCon where
    show _ = "<TyCon>"

deriving instance Show PrimOp
deriving instance Show PrimOpVecCat

data Derived
    = Id `LetFrom` Id
    | Lambda Id
    | Case Id
    | Eta
    | Skolem Id
    | TvSkolem Id
    | Unknown
    | GenTyVar
    | Id `Fix` BW
  deriving (Eq,Ord,Show,Generic)

-- we turn {f = .. f ..}
-- into    {fB = .. fW ..}
data BW = B | W
  deriving (Eq,Ord,Show,Generic)

mkLetFrom :: Id -> Integer -> Id -> Id
mkLetFrom x _ (Derived Unknown _) = x
mkLetFrom x i y                   = Derived (x `LetFrom` y) i

disambigPrim "Integer" = "ghc_Integer"
disambigPrim "Bool"    = "ghc_Bool"
disambigPrim s         = s

originalId :: Id -> String
originalId i = case i of
    GHCOrigin nm _ _ -> disambigPrim (getOccString nm)
    GHCPrim op     -> show op -- "PRIM_" ++ occNameString (primOpOcc op)
    OtherPrim op   -> show op -- "PRIM_" ++ occNameString (primOpOcc op)
    FromProverBool -> "convert"
    ProverBool     -> "bool"
    Const 0 2      -> "const"
    Const i j      -> "const_" ++ show i ++ "_" ++ show j
    Derived d _    -> case d of
        _ `LetFrom` b -> originalId b ++ "_"
        Lambda a      -> originalId a ++ "_lambda"
        Case a        -> originalId a ++ "_case"
        Skolem a      -> originalId a
        TvSkolem a    -> map toUpper (originalId a)
        Eta           -> "x"
        Unknown       -> "u"
        GenTyVar      -> "a"
        f `Fix` _bw   -> "{" ++ originalId f ++ "}"

-- | Pretty prints an Id.
--   Not necessarily to a unique String, the Renamer takes care of proper
--   disabiguation.
ppId :: Id -> String
ppId i = case i of
    GHCOrigin nm _ _ -> disambigPrim (ppName nm)
    GHCPrim op     -> show op
    OtherPrim op   -> show op
    FromProverBool -> "convert"
    ProverBool     -> "bool"
    Derived d x    -> ppDerived x d
    Const 0 2      -> "const"
    Const i j      -> "const_" ++ show i ++ "_" ++ show j

ppDerived :: Integer -> Derived -> String
ppDerived i d = case d of
    f `LetFrom` g -> (case ppId g of { [] -> ""; s -> s ++ "_" }) ++ ppId f
    Lambda f      -> "lam_" ++ ppId f
    Case f        -> "case_" ++ ppId f
    Eta           -> "eta"
    Skolem x      -> ppId x
    TvSkolem x    -> map toUpper (ppId x)
    GenTyVar      -> [['a'..'z'] !! (fromInteger i `mod` 26)]
    Unknown       -> "unknown"
    f `Fix` bw    -> ppId f ++ show bw

ppName :: Name -> String
ppName nm -- = getOccString nm {- ++ '_': showOutputable (getUnique nm) -}
    | k == listTyConKey      = "List"
    | k == nilDataConKey     = "Nil"
    | k == consDataConKey    = "Cons"
    | k == unitTyConKey      = "UnitTyCon"
    | k == genUnitDataConKey = "Unit"
    | otherwise = case getOccString nm of
        "(,)"  -> "Tup"
        "(,,)" -> "Trip"
        "+"   -> "plus"
        "-"   -> "minus"
        "/"   -> "div"
        "*"   -> "mult"
        "^"   -> "pow"
        "++"  -> "append"
        ">>=" -> "bind"
        "=<<" -> "dnib"
        ">=>" -> "dot_monadic"
        "<=<" -> "monadic_dot"
        "<*>" -> "ap"
        "<$>" -> "fmap"
        ">>"  -> "then"
        "||"  -> "or"
        "&&"  -> "and"
        "."   -> "dot"
        "=="  -> "equal"
        "/="  -> "unequal"
        ">"   -> "gt"
        ">="  -> "ge"
        "<"   -> "lt"
        "<="  -> "le"
        "$"   -> "apply"
        "!!"  -> "index"
        "\\\\" -> "difference"
        s     -> s
  where
    k = getUnique nm
-}
