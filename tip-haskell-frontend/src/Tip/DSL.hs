{-# LANGUAGE GADTs #-}
-- | The language properties are expressed in in the Haskell source
module Tip.DSL
    ( Prop
    , (=:=)
    , (==>)
    , proveBool
    , givenBool
    , given
    ) where

infix 1 =:=

infixr 0 ==>

-- | The property data type
data Prop a where
    Given :: Prop b -> Prop a -> Prop a
    (:=:) :: a -> a -> Prop a

-- | A synonym for '==>'
given :: Prop b -> Prop a -> Prop a
given = Given

-- | A synonomy for '==>', but for booleans
givenBool :: Bool -> Prop a -> Prop a
givenBool b = Given (b =:= True)

-- | Implication
(==>) :: Prop b -> Prop a -> Prop a
(==>) = Given

-- | A synonym for '=:=', but for booleans
proveBool :: Bool -> Prop Bool
proveBool lhs = lhs =:= True

-- | Equality
(=:=) :: a -> a -> Prop a
(=:=) = (:=:)

