{-# LANGUAGE PackageImports, MagicHash, FlexibleInstances #-}
module Prelude(
  Bool(..), Maybe(..), Either(..), Ordering(..),
  String, Int, Integer, Float, Double, Rational,
  Eq, (==), (/=),
  Ord, compare, (<), (<=), (>=), (>), max, min,
  Num, (+), (-), (*), negate, abs, signum, fromInteger,
  Real, toRational,
  Integral, quot, rem, div, mod, quotRem, divMod, toInteger,
  Fractional, (/), recip, fromRational,
  Enum, succ, pred, enumFromTo,
  maybe, either,
  (&&), (||), not, otherwise,
  subtract, even, odd, gcd, lcm, (^), (^^),
  fromIntegral, realToFrac,
  fst, snd, curry, uncurry, id, const, (.), flip, ($), until,
  asTypeOf, error, undefined,
  seq, ($!),
  map, (++), filter, concat, concatMap,
  head, last, tail, init, null, length, (!!),
  foldl, foldl1, scanl, scanl1, foldr, foldr1, scanr, scanr1,
  iterate, repeat, replicate, cycle,
  take, drop, splitAt, takeWhile, dropWhile, span, break,
  reverse, and, or,
  any, all, elem, notElem, lookup,
  sum, product, maximum, minimum,
  zip, zip3, zipWith, zipWith3, unzip, unzip3,


  -- These ones are unsupported but provided for Isabelle
  (**), return, (>>=), (>>), (=<<),
  -- These are exported so that deriving Read/Show works
  Read(..), Show(..)) where

import qualified "base" Prelude as P
import "base" Prelude(Bool(..), Read(..), Show(..), String, Eq, Ord, Ordering(..), Enum)
import Tip.GHC.Annotations
import Prelude.Prim
import Tip

default (Integer, Float)

----------------------------------------------------------------------
-- Stuff which is changed from the Haskell report.
----------------------------------------------------------------------

type Int = Integer

type Float = Rational
type Double = Rational

instance Eq Integer where
  (==) = primEquals
  (/=) = primDistinct
instance Eq Rational where
  (==) = primEquals
  (/=) = primDistinct

{-# ANN (==) Inline #-}
{-# ANN (/=) Inline #-}
(==), (/=) :: a -> a -> Bool
(==) = primEquals
(/=) = primDistinct

instance Ord Integer where
  compare = compare
instance Ord Rational where
  compare = compare

{-# ANN (<=) Inline #-}
{-# ANN (<) Inline #-}
{-# ANN (>=) Inline #-}
{-# ANN (>) Inline #-}
(<=), (<), (>=), (>) :: Ord a => a -> a -> Bool
(<=) = primLe
(>=) = primGe
(<)  = primLt
(>)  = primGt

class (P.Num a, Ord a) => Num a where
instance Num Integer
instance Num Rational
instance P.Num Integer where
  fromInteger = primCast
  (+) = (+)
  (-) = (-)
  (*) = (*)
  abs = abs
  signum = signum
instance P.Num Rational where
  fromInteger = primCast
  (+) = (+)
  (-) = (-)
  (*) = (*)
  abs = abs
  signum = signum

-- All uses of fromInteger MUST be monomorphic or inlined.
-- This is because tip-ghc looks at the source and target types
-- of primCast to decide what code to generate.
--
-- This in turn means that almost all of the Prelude numeric functions
-- must be marked inline.
{-# ANN fromInteger Inline #-}
fromInteger :: Num a => Integer -> a
fromInteger = primCast

{-# ANN (+) Inline #-}
{-# ANN (-) Inline #-}
{-# ANN (*) Inline #-}
(+), (-), (*) :: Num a => a -> a -> a
(+) = primPlus
(-) = primMinus
(*) = primTimes

{-# ANN negate Inline #-}
negate :: Num a => a -> a
negate x = 0 - x

class Num a => Real a
instance Real Integer
instance Real Rational

{-# ANN toRational Inline #-}
toRational :: Real a => a -> Rational
toRational = primCast

instance Enum Integer where
  succ = succ
  pred = pred
  enumFromTo = enumFromTo

class (Real a, Enum a) => Integral a
instance Integral Integer

{-# ANN quot Inline #-}
{-# ANN rem Inline #-}
{-# ANN div Inline #-}
{-# ANN mod Inline #-}
{-# ANN quotRem Inline #-}
{-# ANN divMod Inline #-}
{-# ANN toInteger Inline #-}
quot, rem        :: Integral a => a -> a -> a
n `quot` d       =  q  where (q,r) = quotRem n d
n `rem` d        =  r  where (q,r) = quotRem n d

div, mod         :: Integral a => a -> a -> a
div = primDiv
mod = primMod

quotRem, divMod  :: Integral a => a -> a -> (a,a)
-- Here we use the fact that Integer is the only Integral instance
quotRem n d = primCast (primQuotRem (primCast n) (primCast d))

primQuotRem :: Integer -> Integer -> (Integer, Integer)
primQuotRem n d
  | signum n == -signum d && md /= 0 =
    (dv + 1, md - d)
  | otherwise = (dv, md)
  where
    md = n `mod` d
    dv = n `div` d

divMod x y = (div x y, mod x y)

toInteger        :: Integral a => a -> Integer
toInteger x = primCast x

class Num a => Fractional a
instance Fractional Rational

{-# ANN (/) Inline #-}
{-# ANN recip Inline #-}
{-# ANN fromRational Inline #-}
(/) :: Fractional a => a -> a -> a
(/) = primQuotient

recip :: Fractional a => a -> a
recip x = 1 / x

fromRational :: Fractional a => Rational -> a
fromRational = primCast

instance P.Fractional Rational where
  fromRational = P.fromRational
  recip = P.recip

(**) :: Fractional a => a -> a -> a
(**) = error "(**) not supported"

return :: a -> b
return = error "return not supported"

(>>=) :: a -> (b -> c) -> d
(>>=) = error "(>>=) not supported"

(>>) :: a -> b -> b
(>>) = error "(>>) not supported"

(=<<) :: (a -> b) -> c -> d
(=<<) = error "(=<<) not supported"

{-# ANN seq Inline #-}
seq :: a -> b -> b
seq x y = y

{-# ANN (&&) Inline #-}
{-# ANN (||) Inline #-}
{-# ANN not  Inline #-}
(&&), (||)       :: Bool -> Bool -> Bool
(&&) = primAnd
(||) = primOr
not  = primNot

{-# ANN succ Inline #-}
{-# ANN pred Inline #-}
{-# ANN enumFromTo Inline #-}
{-# ANN primSucc Inline #-}
{-# ANN primPred Inline #-}

succ :: Integral a => a -> a
succ x = primCast (primSucc (primCast x))
pred x = primCast (primPred (primCast x))

enumFromTo :: Integral a => a -> a -> [a]
enumFromTo x y = primCast (primEnumFromTo (primCast x) (primCast y))

primSucc, primPred :: Int -> Int
primSucc n = 1+n
primPred n = n-1

primEnumFromTo :: Int -> Int -> [Int]
primEnumFromTo m n
  | m > n = []
  | otherwise = m:primEnumFromTo (succ m) n

----------------------------------------------------------------------
-- Stuff which is taken verbatim from the Haskell report
-- (more or less).
----------------------------------------------------------------------

infixr 9  .
infixr 8  ^, ^^, **
infixl 7  *, /, `quot`, `rem`, `div`, `mod`
infixl 6  +, -

-- The (:) operator is built-in syntax, and cannot legally be given
-- a fixity declaration; but its fixity is given by:
--   infixr 5  :

infix  4  ==, /=, <, <=, >=, >
infixr 3  &&
infixr 2  ||
infixl 1  >>, >>=
infixr 1  =<<
infixr 0  $, $!, `seq`

-- Standard types, classes, instances and related functions

{-# ANN compare Inline #-}
compare :: Ord a => a -> a -> Ordering
compare x y
  | x == y = EQ
  | x <= y = LT
  | otherwise = GT


-- Numeric functions

{-# ANN min Inline #-}
{-# ANN max Inline #-}
min, max :: Ord a => a -> a -> a
max x y
  | x <= y    = y
  | otherwise = x
min x y
  | x <= y    = x
  | otherwise = y

{-# ANN abs Inline #-}
abs :: Num a => a -> a
abs x = if x >= 0 then x else negate x

{-# ANN signum Inline #-}
signum :: Num a => a -> a
signum x =
  case compare x 0 of
    LT -> -1
    EQ -> 0
    GT -> 1


{-# ANN subtract Inline #-}
subtract         :: (Num a) => a -> a -> a
subtract         =  flip (-)


{-# ANN even Inline #-}
{-# ANN odd Inline #-}
even, odd        :: (Integral a) => a -> Bool
even n           =  n `rem` 2 == 0
odd              =  not . even


gcd              :: (Integral a) => a -> a -> a
gcd x y = primCast (primGcd (primCast x) (primCast y))

primGcd :: Integer -> Integer -> Integer
primGcd 0 0          =  error "Prelude.gcd: gcd 0 0 is undefined"
primGcd x y          =  gcd' (abs x) (abs y)
                    where gcd' x 0  =  x
                          gcd' x y  =  gcd' y (x `rem` y)


{-# ANN lcm Inline #-}
lcm              :: (Integral a) => a -> a -> a
lcm x y = primCast (primLcm (primCast x) (primCast y))

primLcm :: Integer -> Integer -> Integer
primLcm _ 0          =  0
primLcm 0 _          =  0
primLcm x y          =  abs ((x `quot` (gcd x y)) * y)


{-# ANN (^) Inline #-}
(^)              :: (Num a, Integral b) => a -> b -> a
x ^ n | n >= 0 = pow x n
  where
    pow x 0 = 1
    pow x n = x * pow x (n-1)


{-# ANN (^^) Inline #-}
(^^)             :: (Fractional a, Integral b) => a -> b -> a
x ^^ n           =  if n >= 0 then x^n else recip (x^(-n))


{-# ANN fromIntegral Inline #-}
fromIntegral     :: (Integral a, Num b) => a -> b
fromIntegral     =  fromInteger . toInteger


{-# ANN realToFrac Inline #-}
realToFrac     :: (Real a, Fractional b) => a -> b
realToFrac      =  fromRational . toRational


-- Function type

-- identity function

{-# ANN id Inline #-}
id               :: a -> a
id x             =  x

-- constant function

{-# ANN const Inline #-}
const            :: a -> b -> a
const x _        =  x

-- function composition

{-# ANN (.) Inline #-}
(.)              :: (b -> c) -> (a -> b) -> a -> c
f . g            =  \ x -> f (g x)

-- flip f  takes its (first) two arguments in the reverse order of f.

{-# ANN flip Inline #-}
flip             :: (a -> b -> c) -> b -> a -> c
flip f x y       =  f y x


-- right-associating infix application operators
-- (useful in continuation-passing style)

{-# ANN ($) Inline #-}
{-# ANN ($!) Inline #-}
($), ($!) :: (a -> b) -> a -> b
f $  x    =  f x
f $! x    =  x `seq` f x


-- Boolean functions


{-# ANN otherwise Inline #-}
otherwise        :: Bool
otherwise        =  True


-- Maybe type


data  Maybe a  =  Nothing | Just a      deriving (Eq, Ord, Read, Show)


{-# ANN maybe Inline #-}
maybe              :: b -> (a -> b) -> Maybe a -> b
maybe n f Nothing  =  n
maybe n f (Just x) =  f x

-- Either type


data  Either a b  =  Left a | Right b   deriving (Eq, Ord, Read, Show)


{-# ANN either Inline #-}
either               :: (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left x)  =  f x
either f g (Right y) =  g y

-- Ordering type


{-# ANN fst Inline #-}
fst              :: (a,b) -> a
fst (x,y)        =  x


{-# ANN snd Inline #-}
snd              :: (a,b) -> b
snd (x,y)        =  y

-- curry converts an uncurried function to a curried function;
-- uncurry converts a curried function to a function on pairs.

{-# ANN curry Inline #-}
curry            :: ((a, b) -> c) -> a -> b -> c
curry f x y      =  f (x, y)


{-# ANN uncurry Inline #-}
uncurry          :: (a -> b -> c) -> ((a, b) -> c)
uncurry f p      =  f (fst p) (snd p)

-- Misc functions

-- until p f  yields the result of applying f until p holds.

until            :: (a -> Bool) -> (a -> a) -> a -> a
until p f x
  | p x = x
  | otherwise = until p f (f x)

-- asTypeOf is a type-restricted version of const.  It is usually used
-- as an infix operator, and its typing forces its first argument
-- (which is usually overloaded) to have the same type as the second.

{-# ANN asTypeOf Inline #-}
asTypeOf         :: a -> a -> a
asTypeOf         =  const

-- error stops execution and displays an error message

{-# ANN error Inline #-}
error            :: String -> a
error _          =  primError

-- It is expected that compilers will recognize this and insert error
-- messages that are more appropriate to the context in which undefined
-- appears.


{-# ANN undefined Inline #-}
undefined        :: a
undefined        =  error "Prelude.undefined"

infixl 9  !!
infixr 5  ++
infix  4  `elem`, `notElem`

{-# NOINLINE map #-}
map :: (a -> b) -> [a] -> [b]
map f = aux
  where
    aux [] = []
    aux (x:xs) = f x:aux xs

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

{-# NOINLINE filter #-}
filter :: (a -> Bool) -> [a] -> [a]
filter p = aux
  where
    aux [] = []
    aux (x:xs)
      | p x = x:aux xs
      | otherwise = aux xs

concat :: [[a]] -> [a]
concat xss = inline foldr (++) [] xss


concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f xss = inline foldr_map (++) [] f xss

-- head and tail extract the first element and remaining elements,
-- respectively, of a list, which must be non-empty.  last and init
-- are the dual functions working from the end of a finite list,
-- rather than the beginning.


head             :: [a] -> a
head (x:_)       =  x
head []          =  error "Prelude.head: empty list"


tail             :: [a] -> [a]
tail (_:xs)      =  xs
tail []          =  error "Prelude.tail: empty list"


last             :: [a] -> a
last [x]         =  x
last (_:xs)      =  last xs
last []          =  error "Prelude.last: empty list"


init             :: [a] -> [a]
init [x]         =  []
init (x:xs)      =  x : init xs
init []          =  error "Prelude.init: empty list"


null             :: [a] -> Bool
null []          =  True
null (_:_)       =  False

-- length returns the length of a finite list as an Int.

length           :: [a] -> Int
length []        =  0
length (_:l)     =  1 + length l

-- List index (subscript) operator, 0-origin

(!!)                :: [a] -> Int -> a
xs     !! n | n < 0 =  error "Prelude.!!: negative index"
[]     !! _         =  error "Prelude.!!: index too large"
(x:_)  !! 0         =  x
(_:xs) !! n         =  xs !! (n-1)

-- foldl, applied to a binary operator, a starting value (typically the
-- left-identity of the operator), and a list, reduces the list using
-- the binary operator, from left to right:
--  foldl f z [x1, x2, ..., xn] == (...((z `f` x1) `f` x2) `f`...) `f` xn
-- foldl1 is a variant that has no starting value argument, and  thus must
-- be applied to non-empty lists.  scanl is similar to foldl, but returns
-- a list of successive reduced values from the left:
--      scanl f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
-- Note that  last (scanl f z xs) == foldl f z xs.
-- scanl1 is similar, again without the starting element:
--      scanl1 f [x1, x2, ...] == [x1, x1 `f` x2, ...]


{-# NOINLINE foldl #-}
foldl            :: (a -> b -> a) -> a -> [b] -> a
foldl f = aux
  where
    aux z [] = z
    aux z (x:xs) = aux (f z x) xs


foldl1           :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs)  =  inline foldl f x xs
foldl1 _ []      =  error "Prelude.foldl1: empty list"


scanl            :: (a -> b -> a) -> a -> [b] -> [a]
scanl f q xs     =  q : (case xs of
                            []   -> []
                            x:xs -> scanl f (f q x) xs)


scanl1           :: (a -> a -> a) -> [a] -> [a]
scanl1 f (x:xs)  =  scanl f x xs
scanl1 _ []      =  []

-- foldr, foldr1, scanr, and scanr1 are the right-to-left duals of the
-- above functions.


{-# NOINLINE foldr #-}
foldr            :: (a -> b -> b) -> b -> [a] -> b
foldr f z = aux
  where
    aux [] = z
    aux (x:xs) = f x (aux xs)

{-# NOINLINE foldr_map #-}
foldr_map :: (a -> b -> b) -> b -> (c -> a) -> [c] -> b
foldr_map op e f = aux
  where
    aux [] = e
    aux (x:xs) = op (f x) (aux xs)

foldr1           :: (a -> a -> a) -> [a] -> a
foldr1 f [x]     =  x
foldr1 f (x:xs)  =  f x (inline foldr1 f xs)
foldr1 _ []      =  error "Prelude.foldr1: empty list"


scanr             :: (a -> b -> b) -> b -> [a] -> [b]
scanr f q0 []     =  [q0]
scanr f q0 (x:xs) =  f x q : qs
                     where qs@(q:_) = scanr f q0 xs


scanr1          :: (a -> a -> a) -> [a] -> [a]
scanr1 f []     =  []
scanr1 f [x]    =  [x]
scanr1 f (x:xs) =  f x q : qs
                   where qs@(q:_) = scanr1 f xs

-- iterate f x returns an infinite list of repeated applications of f to x:
-- iterate f x == [x, f x, f (f x), ...]

iterate          :: (a -> a) -> a -> [a]
iterate f x      =  x : iterate f (f x)

-- repeat x is an infinite list, with x the value of every element.

repeat           :: a -> [a]
repeat x         =  xs where xs = x:xs

-- replicate n x is a list of length n with x the value of every element

replicate        :: Int -> a -> [a]
replicate n x
  | n < 0 = []
  | otherwise = x:replicate (n-1) x

-- cycle ties a finite list into a circular one, or equivalently,
-- the infinite repetition of the original list.  It is the identity
-- on infinite lists.


cycle            :: [a] -> [a]
cycle []         =  error "Prelude.cycle: empty list"
cycle xs         =  xs' where xs' = xs ++ xs'

-- take n, applied to a list xs, returns the prefix of xs of length n,
-- or xs itself if n > length xs.  drop n xs returns the suffix of xs
-- after the first n elements, or [] if n > length xs.  splitAt n xs
-- is equivalent to (take n xs, drop n xs).


take                   :: Int -> [a] -> [a]
take n _      | n <= 0 =  []
take _ []              =  []
take n (x:xs)          =  x : take (n-1) xs


drop                   :: Int -> [a] -> [a]
drop n xs     | n <= 0 =  xs
drop _ []              =  []
drop n (_:xs)          =  drop (n-1) xs


splitAt                  :: Int -> [a] -> ([a],[a])
splitAt n xs             =  (take n xs, drop n xs)

-- takeWhile, applied to a predicate p and a list xs, returns the longest
-- prefix (possibly empty) of xs of elements that satisfy p.  dropWhile p xs
-- returns the remaining suffix.  span p xs is equivalent to
-- (takeWhile p xs, dropWhile p xs), while break p uses the negation of p.


takeWhile               :: (a -> Bool) -> [a] -> [a]
takeWhile p []          =  []
takeWhile p (x:xs)
            | p x       =  x : takeWhile p xs
            | otherwise =  []


dropWhile               :: (a -> Bool) -> [a] -> [a]
dropWhile p []          =  []
dropWhile p xs@(x:xs')
            | p x       =  dropWhile p xs'
            | otherwise =  xs


span, break             :: (a -> Bool) -> [a] -> ([a],[a])
span p []            = ([],[])
span p xs@(x:xs')
            | p x       =  (x:ys,zs)
            | otherwise =  ([],xs)
                           where (ys,zs) = span p xs'

break p                 =  span (not . p)

-- reverse xs returns the elements of xs in reverse order.  xs must be finite.

reverse          :: [a] -> [a]
reverse xs       =  inline foldr (\x xs -> xs ++ [x]) [] xs

-- and returns the conjunction of a Boolean list.  For the result to be
-- True, the list must be finite; False, however, results from a False
-- value at a finite index of a finite or infinite list.  or is the
-- disjunctive dual of and.

and, or          :: [Bool] -> Bool
and              =  inline foldr (&&) True
or               =  inline foldr (||) False

-- Applied to a predicate and a list, any determines if any element
-- of the list satisfies the predicate.  Similarly, for all.

any, all         :: (a -> Bool) -> [a] -> Bool
any p            =  inline foldr_map (||) False p
all p            =  inline foldr_map (&&) True p

-- elem is the list membership predicate, usually written in infix form,
-- e.g., x `elem` xs.  notElem is the negation.

{-# NOINLINE elem #-}
{-# NOINLINE notElem #-}
elem, notElem    :: a -> [a] -> Bool
elem x           =  inline any (== x)
notElem x        =  inline all (/= x)

-- lookup key assocs looks up a key in an association list.

lookup           :: a -> [(a,b)] -> Maybe b
lookup key []    =  Nothing
lookup key ((x,y):xys)
    | key == x   =  Just y
    | otherwise  =  lookup key xys

-- sum and product compute the sum or product of a finite list of numbers.

{-# ANN sum Inline #-}
{-# ANN product Inline #-}
sum, product     :: (Num a) => [a] -> a
sum              =  inline foldl (+) 0
product          =  inline foldl (*) 1

-- maximum and minimum return the maximum or minimum value from a list,
-- which must be non-empty, finite, and of an ordered type.

{-# ANN maximum Inline #-}
{-# ANN minimum Inline #-}
maximum, minimum :: (Ord a) => [a] -> a
maximum []       =  error "Prelude.maximum: empty list"
maximum xs       =  inline foldl1 max xs

minimum []       =  error "Prelude.minimum: empty list"
minimum xs       =  inline foldl1 min xs

-- zip takes two lists and returns a list of corresponding pairs.  If one
-- input list is short, excess elements of the longer list are discarded.
-- zip3 takes three lists and returns a list of triples.  Zips for larger
-- tuples are in the List library


zip              :: [a] -> [b] -> [(a,b)]
zip              =  inline zipWith (,)


zip3             :: [a] -> [b] -> [c] -> [(a,b,c)]
zip3             =  inline zipWith3 (,,)

-- The zipWith family generalises the zip family by zipping with the
-- function given as the first argument, instead of a tupling function.
-- For example, zipWith (+) is applied to two lists to produce the list
-- of corresponding sums.


{-# NOINLINE zipWith #-}
zipWith          :: (a->b->c) -> [a]->[b]->[c]
zipWith z = aux
  where
    aux (a:as) (b:bs) =  z a b : aux as bs
    aux _ _ = []


{-# NOINLINE zipWith3 #-}
zipWith3         :: (a->b->c->d) -> [a]->[b]->[c]->[d]
zipWith3 z = aux
  where
    aux (a:as) (b:bs) (c:cs) = z a b c : aux as bs cs
    aux _ _ _ = []

-- unzip transforms a list of pairs into a pair of lists.


unzip            :: [(a,b)] -> ([a],[b])
unzip            =  inline foldr (\(a,b) ~(as,bs) -> (a:as,b:bs)) ([],[])


unzip3           :: [(a,b,c)] -> ([a],[b],[c])
unzip3           =  inline foldr (\(a,b,c) ~(as,bs,cs) -> (a:as,b:bs,c:cs))
                          ([],[],[])
