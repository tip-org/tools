{-# LANGUAGE DeriveDataTypeable,FlexibleInstances #-}
-- | A drop-in replacement for Prelude with unfoldings exported, oriented towards Nats
module Tip.Prelude (module Tip, module Tip.Prelude, Bool(..), Maybe(..), Either(..), Int) where

import Prelude (Eq,Ord,Show,Bool(..),Int,Either(..),Maybe(..))
import qualified Prelude as P
import Data.Typeable
import Tip

-- * Booleans

otherwise :: Bool
otherwise = True

infixr 3 &&

(&&) :: Bool -> Bool -> Bool
True && x = x
_    && _ = False

infixr 2 ||

(||) :: Bool -> Bool -> Bool
False || x = x
_     || _ = True

not :: Bool -> Bool
not True = False
not False = True

-- * Nat functions

data Nat = Z | S Nat
  deriving (Eq,Show,Typeable,Ord)

even Z = True
even (S Z) = False
even (S (S x)) = even x

double :: Nat -> Nat
double Z     = Z
double (S x) = S (S (double x))

half :: Nat -> Nat
half Z = Z
half (S Z) = Z
half (S (S n)) = S (half n)

infixr 6 +
infixl 6 -

infixr 7 *

infixr 8 ^

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
Z   * m = Z

(^) :: Nat -> Nat -> Nat
n ^ (S m) = n * n ^ m
n ^ Z     = S Z

-- * Truncated subtraction
(-) :: Nat -> Nat -> Nat
S n - S m = n - m
m   - Z   = m
Z   - _   = Z

infix 4 <
infix 4 <=
infix 4 >
infix 4 >=
infix 4 ==
infix 4 /=

(<) :: Nat -> Nat -> Bool
_ < Z     = False
Z < _     = True
S n < S m = n < m

(<=) :: Nat -> Nat -> Bool
Z   <= _   = True
_   <= Z   = False
S x <= S y = x <= y

(>) :: Nat -> Nat -> Bool
Z > _     = False
_ > Z     = True
S n > S m = n > m

(>=) :: Nat -> Nat -> Bool
_   >= Z   = True
Z   >= _   = False
S x >= S y = x >= y

(==) :: Nat -> Nat -> Bool
Z   == Z   = True
Z   == _   = False
S _ == Z   = False
S x == S y = x == y

(/=) :: Nat -> Nat -> Bool
x /= y = not (x == y)

max :: Nat -> Nat -> Nat
max Z n = n
max m Z = m
max (S n) (S m) = S (max n m)

min :: Nat -> Nat -> Nat
min Z _ = Z
min _ Z = Z
min (S n) (S m) = S (min n m)

-- * List functions on nats

take :: Nat -> [a] -> [a]
take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

drop :: Nat -> [a] -> [a]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

splitAt :: Nat -> [a] -> ([a], [a])
splitAt n xs = (take n xs, drop n xs)

length :: [a] -> Nat
length [] = Z
length (_:xs) = S (length xs)

delete :: Nat -> [Nat] -> [Nat]
delete _ [] = []
delete n (x:xs) =
  case n == x of
    True -> xs
    False -> x : (delete n xs)

deleteAll :: Nat -> [Nat] -> [Nat]
deleteAll _ [] = []
deleteAll n (x:xs) =
  case n == x of
    True -> deleteAll n xs
    False -> x : (deleteAll n xs)

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    _ -> count x ys

nub :: [Nat] -> [Nat]
nub (x:xs) = x:deleteAll x (nub xs)
nub []     = []

index :: [a] -> Nat -> Maybe a
index (x:xs) Z     = Just x
index (x:xs) (S n) = index xs n
index []     _     = Nothing

elem :: Nat -> [Nat] -> Bool
x `elem` [] = False
x `elem` (y:ys) = x == y || x `elem` ys

isPermutation :: [Nat] -> [Nat] -> Bool
[]     `isPermutation` ys = null ys
(x:xs) `isPermutation` ys = x `elem` ys && xs `isPermutation` delete x ys

sorted,ordered,uniqsorted :: [Nat] -> Bool
sorted = ordered
ordered []       = True
ordered [x]      = True
ordered (x:y:xs) = x <= y && ordered (y:xs)
uniqsorted []       = True
uniqsorted [x]      = True
uniqsorted (x:y:xs) = x < y && uniqsorted (y:xs)

unique :: [Nat] -> Bool
unique []     = True
unique (x:xs) = if x `elem` xs then False else unique xs

insert :: Nat -> [Nat] -> [Nat]
insert n [] = [n]
insert n (x:xs) =
  case n <= x of
    True -> n : x : xs
    _    -> x : (insert n xs)

isort :: [Nat] -> [Nat]
isort [] = []
isort (x:xs) = insert x (isort xs)

eqList :: [Nat] -> [Nat] -> Bool
eqList (x:xs) (y:ys) = (x == y) && (xs `eqList` ys)
eqList []     []     = True
eqList _      _      = False

sum :: [Nat] -> Nat
sum [] = Z
sum (x:xs) = x + sum xs

product :: [Nat] -> Nat
product [] = S Z
product (x:xs) = x * product xs

lookup :: Nat -> [(Nat,b)] -> Maybe b
lookup x ((y,b):ys) | x == y    = Just b
                    | otherwise = lookup x ys
lookup x [] = Nothing

-- * Int functions

zeq,zne,zle,zlt,zgt,zge :: Int -> Int -> Bool
zeq = (P.==)
zne = (P./=)
zle = (P.<=)
zlt = (P.<)
zgt = (P.>)
zge = (P.>=)

zplus,zmult,zminus,zmax,zmin :: Int -> Int -> Int
zplus = (P.+)
zmult = (P.*)
zminus = (P.-)
zmax = P.max
zmin = P.min

-- * List functions on Ints

{-# NOINLINE ztake #-}
ztake :: Int -> [a] -> [a]
ztake 0 _      = []
ztake _ []     = []
ztake n (x:xs) = x:ztake (n `zminus` 1) xs

{-# NOINLINE zdrop #-}
zdrop :: Int -> [a] -> [a]
zdrop 0 xs     = xs
zdrop _ []     = []
zdrop n (x:xs) = zdrop (n `zminus` 1) xs

zsplitAt :: Int -> [a] -> ([a], [a])
zsplitAt n xs = (ztake n xs, zdrop n xs)

{-# NOINLINE zlength #-}
zlength :: [a] -> Int
zlength []     = 0
zlength (x:xs) = 1 `zplus` zlength xs

zdelete :: Int -> [Int] -> [Int]
zdelete x [] = []
zdelete x (y:ys)
  | x `zeq` y = ys
  | otherwise = y:zdelete x ys

zdeleteAll :: Int -> [Int] -> [Int]
zdeleteAll _ [] = []
zdeleteAll n (x:xs) =
  case n `zeq` x of
    True -> zdeleteAll n xs
    False -> x : (zdeleteAll n xs)


zcount :: Int -> [Int] -> Nat
zcount x []                 = Z
zcount x (y:xs) | x `zeq` y  = S (zcount x xs)
                | otherwise = zcount x xs

zzcount :: Int -> [Int] -> Int
zzcount x []                 = 0
zzcount x (y:xs) | x `zeq` y = 1 `zplus` zzcount x xs
                 | otherwise = zzcount x xs

znub :: [Int] -> [Int]
znub (x:xs) = x:zdeleteAll x (znub xs)
znub []     = []

zindex :: [a] -> Int -> Maybe a
zindex (x:xs) 0 = Just x
zindex (x:xs) n = zindex xs (n `zminus` 1)
zindex []     _ = Nothing

zelem :: Int -> [Int] -> Bool
x `zelem` [] = False
x `zelem` (y:ys) = x `zeq` y || x `zelem` ys

zisPermutation :: [Int] -> [Int] -> Bool
[]     `zisPermutation` ys = null ys
(x:xs) `zisPermutation` ys = x `zelem` ys && xs `zisPermutation` zdelete x ys

zsorted,zordered,zuniqsorted :: [Int] -> Bool
zordered []       = True
zordered [x]      = True
zordered (x:y:xs) = x `zle` y && zordered (y:xs)

zsorted = zordered

zuniqsorted []       = True
zuniqsorted [x]      = True
zuniqsorted (x:y:xs) = x `zlt` y && zuniqsorted (y:xs)

zunique :: [Int] -> Bool
zunique []     = True
zunique (x:xs) = if x `zelem` xs then False else zunique xs

zinsert :: Int -> [Int] -> [Int]
zinsert n [] = [n]
zinsert n (x:xs) =
  case n `zle` x of
    True -> n : x : xs
    _    -> x : (zinsert n xs)

zisort :: [Int] -> [Int]
zisort [] = []
zisort (x:xs) = zinsert x (zisort xs)

zeqList :: [Int] -> [Int] -> Bool
zeqList (x:xs) (y:ys) = (x `zeq` y) && (xs `zeqList` ys)
zeqList []     []     = True
zeqList _      _      = False

zsum :: [Int] -> Int
zsum [] = 0
zsum (x:xs) = x `zplus` zsum xs

zproduct :: [Int] -> Int
zproduct [] = 1
zproduct (x:xs) = x `zmult` zproduct xs

zlookup :: Int -> [(Int,b)] -> Maybe b
zlookup x ((y,b):ys) | x `zeq` y    = Just b
                     | otherwise = zlookup x ys
zlookup x [] = Nothing

-- * Polymorphic lists functions

{-# NOINLINE null #-}
null :: [a] -> Bool
null [] = True
null _  = False

infixr 5 ++

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]

zip :: [a] -> [b] -> [(a, b)]
zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

filter :: (a -> Bool) -> [a] -> [a]
filter p [] = []
filter p (x:xs) | p x = x:filter p xs
filter p (x:xs) = filter p xs


map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x:map f xs

concat :: [[a]] -> [a]
concat (xs:xss) = xs ++ concat xss
concat []       = []

concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f (x:xs) = f x ++ concatMap f xs
concatMap _ []     = []

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

-- * Lists and booleans

and :: [Bool] -> Bool
and (x:xs) = x && and xs
and []     = True

or :: [Bool] -> Bool
or (x:xs) = x || or xs
or []     = False

all :: (a -> Bool) -> [a] -> Bool
all p []     = True
all p (x:xs) = p x && all p xs

any :: (a -> Bool) -> [a] -> Bool
any p []     = False
any p (x:xs) = p x || any p xs

takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs) =
  case p x of
    True -> x : (takeWhile p xs)
    _ -> []

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ [] = []
dropWhile p (x:xs) =
  case p x of
    True -> dropWhile p xs
    _ -> x:xs

-- | Miscellaneous

id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

infixr 9 .

(.) :: (b -> c) -> (a -> b) -> a -> c
f . g = \ x -> f (g x)

flip :: (a -> b -> c) -> (b -> a -> c)
flip f x y = f y x

infixr 0 $
($) :: (a -> b) -> a -> b
f $ x = f x

maybe :: b -> (a -> b) -> Maybe a -> b
maybe n _ Nothing  = n
maybe _ j (Just x) = j x

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x)  = f x
either _ g (Right y) = g y

fst :: (a,b) -> a
fst (x,_) = x

snd :: (a,b) -> b
snd (_,y) = y

