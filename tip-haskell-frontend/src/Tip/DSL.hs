{-# LANGUAGE GADTs #-}
module Tip.DSL
    ( Prop
    , (=:=)
    , proveBool
    , given
    , givenBool
    , (==>)
    ) where

infix 1 =:=

infixr 0 ==>

data Prop a where
    Given :: Prop b -> Prop a -> Prop a
    (:=:) :: a -> a -> Prop a

given :: Prop b -> Prop a -> Prop a
given = Given

givenBool :: Bool -> Prop a -> Prop a
givenBool b = Given (b =:= True)

(==>) :: Prop b -> Prop a -> Prop a
(==>) = Given

proveBool :: Bool -> Prop Bool
proveBool lhs = lhs =:= True

(=:=) :: a -> a -> Prop a
(=:=) = (:=:)

