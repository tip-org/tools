-- Remove "prove" constructs from file.
{-# LANGUAGE PatternGuards #-}
module Tip.Deprove where

import Tip
import Tip.Fresh
import Control.Monad
import Data.Generics.Geniplate

deprove :: Name a => Theory a -> Fresh (Theory a)
deprove thy =
  foldM deprove1
    thy { thy_form_decls = filter (not . isProve) (thy_form_decls thy) }
    (filter isProve (thy_form_decls thy))
  where
    isProve (Formula Prove _ form) = True
    isProve _ = False

    deprove1 thy (Formula Prove tvs form) = do
      tvs' <- mapM (refreshNamed "sk_") tvs
      return thy {
        thy_form_decls = Formula Assert [] (neg (makeTyCons (zip tvs tvs') form)):thy_form_decls thy,
        thy_abs_type_decls = [ AbsType tv 0 | tv <- tvs' ] ++ thy_abs_type_decls thy }

    makeTyCons tvs =
      transformTypeInExpr $ \ty ->
        case ty of
          TyVar tv | Just tv' <- lookup tv tvs -> TyCon tv' []
          _ -> ty
