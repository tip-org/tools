{-# LANGUAGE RecordWildCards #-}
module Tip.Pass.Uncurry(uncurryTheory) where

import Tip
import Tip.Fresh
import Tip.WorkerWrapper

-- | Replace "fat arrow", @=>@, functions with normal functions wherever possible.
uncurryTheory :: Name a => Theory a -> Fresh (Theory a)
uncurryTheory thy =
  workerWrapperFunctions outerUncurryWW thy >>=
  workerWrapperFunctions innerUncurryWW

-- Transform A -> B => C into A B -> C.
outerUncurryWW :: Name a => Function a -> Maybe (Fresh (WorkerWrapper a))
outerUncurryWW func@Function{func_res = args :=>: res, ..} = Just $ do
  lcls <- mapM freshLocal args
  return WorkerWrapper {
    ww_func = func,
    ww_args = func_args ++ lcls,
    ww_res  = res,
    ww_def  = \e -> apply e (map Lcl lcls),
    ww_use  =
      \hd@(Gbl Global{..}) orig_args -> do
        new_args <- mapM (freshLocal . applyType func_tvs gbl_args) args
        return (Lam new_args (hd :@: (orig_args ++ map Lcl new_args)))
  }
outerUncurryWW _ = Nothing

-- Transform A => B => C into A B => C.
innerUncurryWW :: Name a => Function a -> Maybe (Fresh (WorkerWrapper a))
innerUncurryWW _func = Nothing
