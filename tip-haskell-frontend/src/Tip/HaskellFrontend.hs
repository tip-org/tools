{-# LANGUAGE RecordWildCards, DisambiguateRecordFields, NamedFieldPuns #-}
-- | The Haskell frontend to Tip
module Tip.HaskellFrontend(readHaskellFile,Id(..),module Tip.Params) where

import Tip.Core
import Tip.Calls
import Tip.Compile
import Tip.CoreToTip
import Tip.Dicts (inlineDicts)
import Tip.FreeTyCons
import Tip.Id
import Tip.Params
import Tip.ParseDSL
import Tip.Property
import Tip.RemoveDefault
import Tip.Unfoldings
import Tip.Uniquify
import Tip.GHCUtils
import Tip.Pretty

import Control.Monad
import Data.Char
import Data.List (partition,union,delete)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (isNothing)
import System.Directory
import System.Exit

import qualified Id as GHC
import qualified CoreSubst as GHC
import Var (Var)
import TyCon (isAlgTyCon,isClassTyCon,tyConName)
import TysWiredIn (boolTyCon)
import UniqSupply

-- | Transforms a Haskell file to a Tip Theory, crashing if unsuccessful
readHaskellFile :: Params -> IO (Theory Id)
readHaskellFile params@Params{..} = do

    -- whenFlag params PrintParams $ putStrLn (ppShow params)

    -- maybe (return ()) setCurrentDirectory directory

    prop_ids <- compileHaskellFile params

    let vars = filterVarSet (not . varInTip) $
               unionVarSets (map (transCalls Without) prop_ids)

    us0 <- mkSplitUniqSupply 'h'

    let (binds,_us1) = initUs us0 $ sequence
            [ fmap ((,) v) (runUQ . uqExpr <=< rmdExpr $ inlineDicts e)
            | v <- varSetElems vars
            , isNothing (GHC.isClassOpId_maybe v)
            , Just e <- [maybeUnfolding v]
            ]

        tcs = filter (\ x -> isAlgTyCon x && not (nameInTip (tyConName x)) && not (isClassTyCon x))
                     (delete boolTyCon (bindsTyCons' binds))

    when (PrintCore `elem` flags) $ do
        putStrLn "Tip.HaskellFrontend, PrintInitialTip:"
        putStrLn (showOutputable binds)

    let tip_data =
          [ case trTyCon tc of
              Right tc' -> tc'
              Left err -> error $ showOutputable tc ++ ": " ++ err
          | tc <- tcs
          ]

    let tip_fns0 = concat
          [ case runTM (trDefn v e) of
              Right fn -> fn
              Left err -> error $ showOutputable v ++ ": " ++ err
          | (v,e) <- binds
          ]

        -- Now, split these into properties and non-properties
    let (prop_fns,tip_fns) = partition (isPropType . func_res) tip_fns0

        tip_props = either error id (mapM trProperty prop_fns)

        thy = Theory tip_data [] [] tip_fns tip_props

    when (PrintInitialTip `elem` flags) $ do
        putStrLn "Tip.HaskellFrontend, PrintInitialTip:"
        putStrLn (ppRender thy)

    return thy

