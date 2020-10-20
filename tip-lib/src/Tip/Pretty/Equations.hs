{-# LANGUAGE RecordWildCards #-}
module Tip.Pretty.Equations where

import Tip.Core
import Tip.Scope
import Tip.Pretty
import Text.PrettyPrint
import Data.List
import Data.Char
import Tip.Pretty.SMT()

stripModule :: String -> String
stripModule = reverse . takeWhile (/= '.') . reverse

ppEquations :: (Ord a, PrettyVar a) => Theory a -> Doc
ppEquations thy@Theory{..} =
  vcat $
    [ pp lemma | lemma <- lemmas ] ++
    [ pp goal | goal <- goals ]
  where
    scp = scope thy

    conjectures = [ form | form@Formula{fm_role = Prove} <- thy_asserts ]
    (lemmas, goals) = partition (hasAttr lemma) conjectures
    
    pp Formula{..} = ppEqn fm_body

    ppEqn (Quant _ Forall _ t) = ppEqn t
    ppEqn (Builtin Implies :@: [t, u]) =
      hang (ppEqn t <+> text "=>") 2 (ppEqn u)
    ppEqn (Builtin Equal :@: [t, u]) =
      hang (ppExpr 0 t <+> text "=") 2 (ppExpr 0 u)
    ppEqn t = ppExpr 0 t

    ppExpr _ (Lcl x) =
      ppVar (lcl_name x)
    ppExpr n (Gbl f :@: ts) =
      ppFunc n (name (gbl_name f)) ts
    ppExpr n (Builtin NumAdd :@: ts) =
      ppFunc n "+" ts
    ppExpr n (Builtin NumMul :@: ts) =
      ppFunc n "*" ts
    ppExpr n (Builtin (Lit (Int m)) :@: ts) =
      ppFunc n (show m) ts

    name f =
      case getAttr source (whichGlobal f scp) of
        Just name -> stripModule name
        Nothing -> varStr f

    ppFunc p f [t, u]
      | not (all isAlphaNum f) =
          parIf (p > 0) (hang (ppExpr 1 t <+> text f) 2 (ppExpr 1 u))
    ppFunc _ f [] = text f
    ppFunc p f ts =
      parIf (p > 1) (hang (text f) 2 (fsep (map (ppExpr 2) ts)))
