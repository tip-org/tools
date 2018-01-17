{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
import qualified Text.Show.Functions
import qualified Data.Ratio as R
import qualified Data.Typeable as T
import qualified GHC.Generics as G
import qualified Prelude as P
import qualified QuickSpec as QS
import qualified Test.Feat as F
import qualified Test.QuickCheck as QC
import qualified Tip.Haskell.GenericArbitrary
data Tree a = Leaf a | Node (Tree a) a (Tree a)
  deriving (P.Eq, P.Ord, P.Show, G.Generic, T.Typeable)
F.deriveEnumerable (''Tree)
instance
  ((T.Typeable a, QC.Arbitrary a, G.Generic a)) =>
    QC.Arbitrary (Tree a)
  where
  arbitrary = Tip.Haskell.GenericArbitrary.genericArbitrary

tmap ::
  forall b c .
    (QC.Arbitrary b, F.Enumerable b, P.Ord b, QC.Arbitrary c,
     F.Enumerable c, P.Ord c) =>
      (b -> c) -> Tree b -> Tree c
tmap x (Leaf z) = Leaf (P.id x z)
tmap x (Node l x2 r) = Node (tmap x l) (P.id x x2) (tmap x r)
mirror ::
  forall a2 .
    (QC.Arbitrary a2, F.Enumerable a2, P.Ord a2) => Tree a2 -> Tree a2
mirror (Leaf y) = Leaf y
mirror (Node l2 z2 p) = Node (mirror p) z2 (mirror l2)
sig =
  ([((QS.constant
        "tmap"
        ((\ QS.Dict -> tmap) ::
           QS.Dict
             (QC.Arbitrary QS.A, F.Enumerable QS.A, P.Ord QS.A,
              QC.Arbitrary QS.B, F.Enumerable QS.B, P.Ord QS.B) ->
             (QS.A -> QS.B) -> Tree QS.A -> Tree QS.B))
       {QS.conSize = 0},
     [(1) :: P.Int, (2) :: P.Int]),
    ((QS.constant
        "mirror"
        ((\ QS.Dict -> mirror) ::
           QS.Dict (QC.Arbitrary QS.A, F.Enumerable QS.A, P.Ord QS.A) ->
             Tree QS.A -> Tree QS.A))
       {QS.conSize = 0},
     [(0) :: P.Int, (2) :: P.Int])],
   QS.signature
     {QS.constants =
        [(QS.constant
            "Leaf"
            ((\ QS.Dict -> Leaf) ::
               QS.Dict (QC.Arbitrary QS.A, F.Enumerable QS.A, P.Ord QS.A) ->
                 QS.A -> Tree QS.A))
           {QS.conSize = 0, QS.conIsBackground = P.True},
         (QS.constant
            "Node"
            ((\ QS.Dict -> Node) ::
               QS.Dict (QC.Arbitrary QS.A, F.Enumerable QS.A, P.Ord QS.A) ->
                 Tree QS.A -> QS.A -> Tree QS.A -> Tree QS.A))
           {QS.conSize = 0, QS.conIsBackground = P.True}],
      QS.instances =
        [QS.makeInstance
           ((\ (QS.Dict, (QS.Dict, (QS.Dict, ()))) -> P.return QS.Dict) ::
              (QS.Dict (QC.Arbitrary QS.A),
               (QS.Dict (F.Enumerable QS.A), (QS.Dict (P.Ord QS.A), ()))) ->
                QC.Gen
                  (QS.Dict (QC.Arbitrary QS.A, F.Enumerable QS.A, P.Ord QS.A))),
         QS.makeInstance
           ((\ (QS.Dict, (QS.Dict, (QS.Dict, ()))) -> P.return QS.Dict) ::
              (QS.Dict (QC.Arbitrary QS.A),
               (QS.Dict (F.Enumerable QS.A), (QS.Dict (P.Ord QS.A), ()))) ->
                QC.Gen
                  (QS.Dict (QC.Arbitrary QS.A, F.Enumerable QS.A, P.Ord QS.A))),
         QS.makeInstance
           ((\ (QS.Dict,
                (QS.Dict, (QS.Dict, (QS.Dict, (QS.Dict, (QS.Dict, ())))))) ->
               P.return QS.Dict) ::
              (QS.Dict (QC.Arbitrary QS.A),
               (QS.Dict (F.Enumerable QS.A),
                (QS.Dict (P.Ord QS.A),
                 (QS.Dict (QC.Arbitrary QS.B),
                  (QS.Dict (F.Enumerable QS.B), (QS.Dict (P.Ord QS.B), ())))))) ->
                QC.Gen
                  (QS.Dict
                     (QC.Arbitrary QS.A, F.Enumerable QS.A, P.Ord QS.A,
                      QC.Arbitrary QS.B, F.Enumerable QS.B, P.Ord QS.B))),
         QS.makeInstance
           ((\ (QS.Dict, (QS.Dict, (QS.Dict, ()))) -> P.return QS.Dict) ::
              (QS.Dict (QC.Arbitrary QS.A),
               (QS.Dict (F.Enumerable QS.A), (QS.Dict (P.Ord QS.A), ()))) ->
                QC.Gen
                  (QS.Dict (QC.Arbitrary QS.A, F.Enumerable QS.A, P.Ord QS.A))),
         QS.baseType (P.undefined :: R.Rational),
         QS.inst ((QS.Sub QS.Dict) :: () QS.:- (F.Enumerable P.Int)),
         QS.inst
           ((QS.Sub QS.Dict) :: (P.Ord QS.A) QS.:- (P.Ord (Tree QS.A))),
         QS.inst
           ((QS.Sub QS.Dict) ::
              (F.Enumerable QS.A) QS.:- (F.Enumerable (Tree QS.A))),
         QS.inst3
           ((QS.Sub QS.Dict) ::
              (T.Typeable QS.A, QC.Arbitrary QS.A, G.Generic QS.A) QS.:-
                (QC.Arbitrary (Tree QS.A)))],
      QS.maxTermSize = P.Just (7),
      QS.maxTermDepth = P.Just (4),
      QS.testTimeout = P.Just (100000)})
main = P.uncurry QS.choppyQuickSpec sig

