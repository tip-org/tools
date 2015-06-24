{-# LANGUAGE RecordWildCards, DisambiguateRecordFields, NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
-- | The Haskell frontend to Tip
module Tip.HaskellFrontend(readHaskellFile,readHaskellOrTipFile,Id(..),module Tip.Params) where

import Language.Haskell.GHC.Simple hiding (Id) -- Thanks, Anton!
import qualified Language.Haskell.GHC.Simple as Simple

import Tip.Utils
import Tip.Id
import Tip.Params
import Tip.Core
import Tip.CoreToTip

import Tip.ParseDSL
import Tip.Property

import Tip.GHCUtils

import CoreFVs
import VarSet
import UniqSupply

import Data.List
import Data.Either

import Tip.Dicts
import Tip.Uniquify
import Tip.RemoveDefault
import Tip.FreeTyCons

import TysWiredIn (boolTyCon,listTyCon)

import Control.Monad

import Tip.GenericInstances
import Data.Generics.Geniplate

import qualified Tip.Parser as TipP

-- | If the file cannot be read as a TIP file, it is instead read as a Haskell file.
readHaskellOrTipFile :: FilePath -> Params -> IO (Either String (Theory (Either TipP.Id Id)))
readHaskellOrTipFile file params =
  do mthy1 <- TipP.parseFile file
     case mthy1 of
       Right thy -> return (Right (fmap Left thy))
       Left err1 ->
         do mthy2 <- readHaskellFile file params
            case mthy2 of
              Right thy -> return (Right (fmap Right thy))
              Left err2 -> return (Left (err1 ++ "\n" ++ err2))

-- | Transforms a Haskell file to a Tip Theory or an error
readHaskellFile :: FilePath -> Params -> IO (Either String (Theory Id))
readHaskellFile file params@Params{..} = do

  let cfg :: CompConfig ModGuts
      cfg = defaultConfig {
          cfgGhcFlags =
            ["-dynamic-too"
            ,"-fno-ignore-interface-pragmas"
            ,"-fno-omit-interface-pragmas"
            ,"-fexpose-all-unfoldings"]
            ++ include
        }

  mres <- compileWith cfg [file]

  case mres of
    Failure errs warns ->
      return . Left . unlines $
        [ showOutputable p ++ ":" ++ m ++ "\n" ++ l
        | Simple.Error p m l <- errs
        ]
    Success cms warns _ ->
      do {- putStrLn $ unlines
            [ showOutputable p ++ ":" ++ m
            | Simple.Warning p m <- warns
            ]
         -}
         readModules params cms

addUnfoldings :: [(Var,CoreExpr)] -> [(Var,CoreExpr)]
addUnfoldings binds | null unfs = binds
                    | otherwise = addUnfoldings (binds ++ unfs)
  where
    unfs = usortOn fst
      [ (x,inlineDicts e')
      | (_,e) <- binds
      , Var x :: CoreExpr <- universeBi e
      , x `notElem` map fst binds
      , Just e' <- [maybeUnfolding x]
      ]

readModules :: Params -> [CompiledModule ModGuts] -> IO (Either String (Theory Id))
readModules params@Params{..} cms = do
  let mgs    = map modCompiledModule cms
  let binds0 = addUnfoldings (map (fmap inlineDicts) (flattenBinds (concatMap mg_binds mgs)))

  us0 <- mkSplitUniqSupply 'h'

  let (binds,_us1) = initUs us0 $ sequence
         [ fmap ((,) v) (runUQ . uqExpr <=< rmdExpr $ e)
         | (v,e) <- binds0
         , not (varInTip v)
         ]

  let the_props  :: [(Var,CoreExpr)]
      the_props =
        [ ve
        | ve@(v,_) <- binds
        , not (varInTip v)
        , varToString v `elem` extra_names
          || (varWithPropType v && maybe True (varToString v `elem`) prop_names)
        ]

  let prop_ids = map fst the_props

  -- Find all bindings transitively from props

  let reachable = transFrom prop_ids binds

  when (PrintCore `elem` debug_flags) $ putStrLn $ showOutputable reachable

  let tycons =
         filter (\ x -> isAlgTyCon x && not (nameInTip (tyConName x)) && not (isClassTyCon x))
                (delete boolTyCon (bindsTyCons reachable))

  let (data_errs,tip_data) =
        partitionEithers
          [ case trTyCon tc of
              Right tc' -> Right tc'
              Left err  -> Left $ showOutputable tc ++ ": " ++ err
          | tc <- tycons
          ]

  let (fn_errs,concat -> tip_fns0) =
        partitionEithers
          [ case runTM (trDefn v e) of
              Right fn -> Right fn
              Left err -> Left $ showOutputable v ++ ": " ++ err
          | (v,e) <- reachable
          , all (not . varFromRealModule v) ["mod","div"]
          ]

  let (prop_fns,tip_fns) = partition (isPropType . func_res) tip_fns0

      (prop_errs,tip_props) = partitionEithers (map trProperty prop_fns)

      thy = Theory tip_data [] [Signature Tip.Id.Error errorType] tip_fns tip_props

      errs = data_errs ++ fn_errs ++ prop_errs

  return (if null errs then Right thy else Left (unlines errs))

transFrom :: [Var] -> [(Var,CoreExpr)] -> [(Var,CoreExpr)]
transFrom (mkVarSet -> s0) binds = filter (\ (v,_) -> v `elemVarSet` fin) binds
  where
  fin = go s0

  go :: VarSet ->  VarSet
  go visited | isEmptyVarSet new = visited
             | otherwise         = go (new `unionVarSet` visited)
    where
    new :: VarSet
    new =
      unionVarSets
        [ exprSomeFreeVars (\ _ -> True) rhs_start
        | v_start <- varSetElems visited
        , Just rhs_start <- [lookup v_start binds]
        ]
      `minusVarSet` visited

