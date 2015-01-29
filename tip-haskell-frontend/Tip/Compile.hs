{-# LANGUAGE RecordWildCards, NamedFieldPuns, CPP #-}
module Tip.Compile (compileHaskellFile) where

import Tip.Calls
import Tip.Dicts (inlineDicts)
import Tip.GHCUtils
import Tip.Params
import Tip.ParseDSL
import Tip.Scope
import Tip.Unfoldings
import Data.List.Split (splitOn)

import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.Foldable as F
import System.FilePath

import CoreMonad (liftIO)
import CoreSyn
import CoreSyn (flattenBinds)
import DynFlags
import GHC
import GHC.Paths
import HscTypes
import SimplCore
import Var
import VarSet
#if __GLASGOW_HASKELL__ < 708
import StaticFlags
#endif

compileHaskellFile :: Params  -> IO [Var]
compileHaskellFile params@Params{..} = do

    -- Notify ghc where ghc is installed
    runGhc (Just libdir) $ do

        -- Set interpreted so we can get the signature,
        -- and expose all unfoldings
        dflags0 <- getSessionDynFlags
        let dflags =
#if __GLASGOW_HASKELL__ >= 708
                updateWays $
                addWay' WayThreaded $
                addWay' WayDyn $
#endif
                     dflags0 { ghcMode = CompManager
                             , optLevel = 1
                             , profAuto = NoProfAuto
                             , importPaths = include ++ includePaths dflags0 ++ ["."]
                             }
                        `wopt_unset` Opt_WarnOverlappingPatterns
#if __GLASGOW_HASKELL__ >= 708
                        `gopt_unset` Opt_IgnoreInterfacePragmas
                        `gopt_unset` Opt_OmitInterfacePragmas
                        `gopt_set` Opt_ExposeAllUnfoldings
                        `xopt_set` Opt_TypeOperators
#else
                        `dopt_unset` Opt_IgnoreInterfacePragmas
                        `dopt_unset` Opt_OmitInterfacePragmas
                        `dopt_set` Opt_ExposeAllUnfoldings
                        `dopt_set` Opt_TypeOperators
#endif
        _ <- setSessionDynFlags dflags

            -- add .hs if it is not present (apparently not supporting lhs)
        let file_with_ext = replaceExtension file ".hs"

        target <- guessTarget file_with_ext Nothing
        addTarget target
        r <- load LoadAllTargets
        when (failed r) $ error "Compilation failed!"

        mod_graph <- getModuleGraph
        let mod_sum = findModuleSum file_with_ext mod_graph

        -- Parse, typecheck and desugar the module
        p <- parseModule mod_sum
        t <- typecheckModule p
        d <- desugarModule t

        let modguts = dm_core_module d

        let binds = fixUnfoldings (inlineDicts (flattenBinds (mg_binds modguts)))

        let fix_id :: Id -> Id
            fix_id = fixId binds

        when (PrintCore `elem` flags)
             (liftIO (putStrLn (showOutputable binds)))

        ids_in_scope <- getIdsInScope fix_id

        let only' :: [String]
            only' = concatMap (splitOn ",") only

            props :: [Var]
            props =
                [ i
                | i <- ids_in_scope
                , varWithPropType i
                , not (varFromPrelude i)
                , null only || varToString i `elem` only'
                ]

        extra_ids <- extraIds params props

        -- Wrapping up
        return (ids_in_scope `union` extra_ids)

findModuleSum :: FilePath -> [ModSummary] -> ModSummary
findModuleSum file
    = fromMaybe (error $ "Cannot find module " ++ file)
    . find (maybe False (== file) . summaryHsFile)

summaryHsFile :: ModSummary -> Maybe FilePath
summaryHsFile = ml_hs_file . ms_location

parseToId :: String -> Ghc Id
parseToId s = do
    t <- lookupString s
    case mapMaybe thingToId t of
        []  -> error $ s ++ " not in scope!"
        [x] -> return x
        xs  -> error $ s ++ " in scope as too many things: " ++ showOutputable xs

extraIds :: Params -> [Var] -> Ghc [Var]
extraIds p@Params{..} prop_ids = do

    extra_trans_ids <- mapM parseToId (concatMap (splitOn ",") extra_trans)

    let trans_ids :: VarSet
        trans_ids = unionVarSets $
            map (transCalls With) (prop_ids ++ extra_trans_ids)

    extra_ids <- mapM parseToId (concatMap (splitOn ",") extra)

    let ids = varSetElems $ filterVarSet (\ x -> not (varFromPrelude x || varWithPropType x) && not (hasClass (varType x)))
            trans_ids `unionVarSet` mkVarSet extra_ids

    -- Filters out silly things like
    -- Control.Exception.Base.patError and GHC.Prim.realWorld#
    let in_scope = inScope . varToString -- see Note unqualified identifiers

    ids_in_scope <- filterM in_scope ids

    liftIO $ when (PrintExtraIds `elem` flags) $ do
        let out :: String -> [Id] -> IO ()
            out lbl os = putStrLn $ lbl ++ " =\n " ++ showOutputable [ (o{-,maybeUnfolding o-}) | o <- os ]
#define OUT(i) out "i" (i)
        OUT(prop_ids)
        OUT(extra_trans_ids)
        OUT(extra_ids)
        OUT(ids)
        OUT(ids_in_scope)
#undef OUT

    return ids_in_scope

