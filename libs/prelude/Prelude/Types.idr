module Prelude.Types

import Builtin
import PrimIO
import Prelude.Basics
import Prelude.EqOrd
import Prelude.Interfaces
import Prelude.Num
import Prelude.Uninhabited

%default total

-----------
-- NATS ---
-----------

||| Natural numbers: unbounded, unsigned integers which can be pattern matched.
public export
data Nat =
  ||| Zero.
    Z
  | ||| Successor.
  S Nat

%name Nat k, j, i

public export
integerToNat : Integer -> Nat
integerToNat x
  = if intToBool (prim__lte_Integer x 0)
       then Z
       else S (assert_total (integerToNat (prim__sub_Integer x 1)))

-- Define separately so we can spot the name when optimising Nats
||| Add two natural numbers.
||| @ x the number to case-split on
||| @ y the other numberpublic export
public export
plus : (1 x : Nat) -> (1 y : Nat) -> Nat
plus Z y = y
plus (S k) y = S (plus k y)

||| Subtract natural numbers.  If the second number is larger than the first,
||| return 0.
public export
minus : (1 left : Nat) -> Nat -> Nat
minus Z        right     = Z
minus left     Z         = left
minus (S left) (S right) = minus left right

||| Multiply natural numbers.
public export
mult : (1 x : Nat) -> Nat -> Nat
mult Z y = Z
mult (S k) y = plus y (mult k y)

public export
Num Nat where
  (+) = plus
  (*) = mult

  fromInteger x = integerToNat x

public export
Eq Nat where
  Z == Z = True
  S j == S k = j == k
  _ == _ = False

public export
Ord Nat where
  compare Z Z = EQ
  compare Z (S k) = LT
  compare (S k) Z = GT
  compare (S j) (S k) = compare j k

public export
natToInteger : Nat -> Integer
natToInteger Z = 0
natToInteger (S k) = 1 + natToInteger k
                         -- integer (+) may be non-linear in second
                         -- argument

-----------
-- PAIRS --
-----------

%inline
public export
Bifunctor Pair where
  bimap f g (x, y) = (f x, g y)

%inline
public export
Functor (Pair a) where
  map = mapSnd

-----------
-- MAYBE --
-----------

||| An optional value.  This can be used to represent the possibility of
||| failure, where a function may return a value, or not.
public export
data Maybe : (ty : Type) -> Type where
  ||| No value stored
  Nothing : Maybe ty

  ||| A value of type `ty` is stored
  Just : (1 x : ty) -> Maybe ty

public export
Uninhabited (Nothing = Just x) where
  uninhabited Refl impossible

public export
Uninhabited (Just x = Nothing) where
  uninhabited Refl impossible

public export
maybe : Lazy b -> Lazy (a -> b) -> Maybe a -> b
maybe n j Nothing  = n
maybe n j (Just x) = j x

public export
Eq a => Eq (Maybe a) where
  Nothing  == Nothing  = True
  Nothing  == (Just _) = False
  (Just _) == Nothing  = False
  (Just a) == (Just b) = a == b

public export
Ord a => Ord (Maybe a) where
  compare Nothing  Nothing  = EQ
  compare Nothing  (Just _) = LT
  compare (Just _) Nothing  = GT
  compare (Just a) (Just b) = compare a b

public export
Semigroup (Maybe a) where
  Nothing   <+> m = m
  (Just x)  <+> _ = Just x

public export
Monoid (Maybe a) where
  neutral = Nothing

public export
Functor Maybe where
  map f (Just x) = Just (f x)
  map f Nothing  = Nothing

public export
Applicative Maybe where
  pure = Just

  Just f <*> Just a = Just (f a)
  _      <*> _        = Nothing

public export
Alternative Maybe where
  empty = Nothing

  (Just x) <|> _ = Just x
  Nothing  <|> v = v

public export
Monad Maybe where
  Nothing  >>= k = Nothing
  (Just x) >>= k = k x

public export
Foldable Maybe where
  foldr _ z Nothing  = z
  foldr f z (Just x) = f x z

public export
Traversable Maybe where
  traverse f Nothing = pure Nothing
  traverse f (Just x) = (pure Just) <*> (f x)

---------
-- DEC --
---------

||| Decidability.  A decidable property either holds or is a contradiction.
public export
data Dec : Type -> Type where
  ||| The case where the property holds.
  ||| @ prf the proof
  Yes : (prf : prop) -> Dec prop

  ||| The case where the property holding would be a contradiction.
  ||| @ contra a demonstration that prop would be a contradiction
  No  : (contra : prop -> Void) -> Dec prop

------------
-- EITHER --
------------

||| A sum type.
public export
data Either : (a : Type) -> (b : Type) -> Type where
  ||| One possibility of the sum, conventionally used to represent errors.
  Left : forall a, b. (1 x : a) -> Either a b

  ||| The other possibility, conventionally used to represent success.
  Right : forall a, b. (1 x : b) -> Either a b

||| Simply-typed eliminator for Either.
||| @ f the action to take on Left
||| @ g the action to take on Right
||| @ e the sum to analyze
public export
either : (f : Lazy (a -> c)) -> (g : Lazy (b -> c)) -> (e : Either a b) -> c
either l r (Left x) = l x
either l r (Right x) = r x

public export
(Eq a, Eq b) => Eq (Either a b) where
  Left x == Left x' = x == x'
  Right x == Right x' = x == x'
  _ == _ = False

public export
(Ord a, Ord b) => Ord (Either a b) where
  compare (Left x) (Left x') = compare x x'
  compare (Left _) (Right _) = LT
  compare (Right _) (Left _) = GT
  compare (Right x) (Right x') = compare x x'

%inline
public export
Functor (Either e) where
  map f (Left x) = Left x
  map f (Right x) = Right (f x)

%inline
public export
Bifunctor Either where
  bimap f _ (Left x) = Left (f x)
  bimap _ g (Right y) = Right (g y)

%inline
public export
Applicative (Either e) where
  pure = Right

  (Left a) <*> _          = Left a
  (Right f) <*> (Right r) = Right (f r)
  (Right _) <*> (Left l)  = Left l

public export
Monad (Either e) where
  (Left n) >>= _ = Left n
  (Right r) >>= f = f r

public export
Foldable (Either e) where
  foldr f acc (Left _) = acc
  foldr f acc (Right x) = f x acc

public export
Traversable (Either e) where
  traverse f (Left x)  = pure (Left x)
  traverse f (Right x) = Right <$> f x

-----------
-- LISTS --
-----------

||| Generic lists.
public export
data List a =
  ||| Empty list
  Nil

  | ||| A non-empty list, consisting of a head element and the rest of the list.
  (::) a (List a)

%name List xs, ys, zs

public export
Eq a => Eq (List a) where
  [] == [] = True
  x :: xs == y :: ys = x == y && xs == ys
  _ == _ = False

public export
Ord a => Ord (List a) where
  compare [] [] = EQ
  compare [] (x :: xs) = LT
  compare (x :: xs) [] = GT
  compare (x :: xs) (y ::ys)
     = case compare x y of
            EQ => compare xs ys
            c => c

namespace List
  public export
  (++) : (1 xs, ys : List a) -> List a
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: xs ++ ys

  public export
  length : List a -> Nat
  length []        = Z
  length (x :: xs) = S (length xs)

public export
Functor List where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

public export
Semigroup (List a) where
  (<+>) = (++)

public export
Monoid (List a) where
  neutral = []

public export
Foldable List where
  foldr c n [] = n
  foldr c n (x::xs) = c x (foldr c n xs)

  foldl f q [] = q
  foldl f q (x::xs) = foldl f (f q x) xs

public export
Applicative List where
  pure x = [x]
  fs <*> vs = concatMap (\f => map f vs) fs

public export
Alternative List where
  empty = []
  (<|>) = (++)

public export
Monad List where
  m >>= f = concatMap f m

public export
Traversable List where
  traverse f [] = pure []
  traverse f (x::xs) = pure (::) <*> (f x) <*> (traverse f xs)

||| Check if something is a member of a list using the default Boolean equality.
public export
elem : Eq a => a -> List a -> Bool
x `elem` [] = False
x `elem` (y :: ys) = x == y ||  elem x ys

-------------
-- STREAMS --
-------------

namespace Stream
  ||| An infinite stream.
  public export
  data Stream : Type -> Type where
       (::) : a -> Inf (Stream a) -> Stream a

public export
Functor Stream where
  map f (x :: xs) = f x :: map f xs

||| The first element of an infinite stream.
public export
head : Stream a -> a
head (x :: xs) = x

||| All but the first element.
public export
tail : Stream a -> Stream a
tail (x :: xs) = xs

||| Take precisely n elements from the stream.
||| @ n how many elements to take
||| @ xs the stream
public export
take : (1 n : Nat) -> (xs : Stream a) -> List a
take Z xs = []
take (S k) (x :: xs) = x :: take k xs

-------------
-- STRINGS --
-------------

namespace Strings
  public export
  (++) : (1 x : String) -> (1 y : String) -> String
  x ++ y = prim__strAppend x y

  ||| Returns the length of the string.
  |||
  ||| ```idris example
  ||| length ""
  ||| ```
  ||| ```idris example
  ||| length "ABC"
  ||| ```
  public export
  length : String -> Nat
  length str = fromInteger (prim__cast_IntInteger (prim__strLength str))

||| Reverses the elements within a string.
|||
||| ```idris example
||| reverse "ABC"
||| ```
||| ```idris example
||| reverse ""
||| ```
public export
reverse : String -> String
reverse = prim__strReverse

||| Returns a substring of a given string
|||
||| @ index The (zero based) index of the string to extract.  If this is beyond
|||         the end of the string, the function returns the empty string.
||| @ len The desired length of the substring.  Truncated if this exceeds the
|||       length of the input
||| @ subject The string to return a portion of
public export
substr : (index : Nat) -> (len : Nat) -> (subject : String) -> String
substr s e subj
    = if natToInteger s < natToInteger (length subj)
         then prim__strSubstr (prim__cast_IntegerInt (natToInteger s))
                              (prim__cast_IntegerInt (natToInteger e))
                              subj
         else ""

||| Adds a character to the front of the specified string.
|||
||| ```idris example
||| strCons 'A' "B"
||| ```
||| ```idris example
||| strCons 'A' ""
||| ```
public export
strCons : Char -> String -> String
strCons = prim__strCons

public export
strUncons : String -> Maybe (Char, String)
strUncons "" = Nothing
strUncons str = assert_total $ Just (prim__strHead str, prim__strTail str)

||| Turns a list of characters into a string.
public export
pack : List Char -> String
pack [] = ""
pack (x :: xs) = strCons x (pack xs)

%foreign
    "scheme:string-pack"
    "javascript:lambda:(xs)=>''.concat(...__prim_idris2js_array(xs))"
export
fastPack : List Char -> String

||| Turns a string into a list of characters.
|||
||| ```idris example
||| unpack "ABC"
||| ```
public export
unpack : String -> List Char
unpack str = unpack' (prim__cast_IntegerInt (natToInteger (length str)) - 1) str []
  where
    unpack' : Int -> String -> List Char -> List Char
    unpack' pos str acc
        = if pos < 0
             then acc
             else assert_total $ unpack' (pos - 1) str (assert_total (prim__strIndex str pos)::acc)

public export
Semigroup String where
  (<+>) = (++)

public export
Monoid String where
  neutral = ""

----------------
-- CHARACTERS --
----------------

||| Returns true if the character is in the range [A-Z].
public export
isUpper : Char -> Bool
isUpper x = x >= 'A' && x <= 'Z'

||| Returns true if the character is in the range [a-z].
public export
isLower : Char -> Bool
isLower x = x >= 'a' && x <= 'z'

||| Returns true if the character is in the ranges [A-Z][a-z].
public export
isAlpha : Char -> Bool
isAlpha x = isUpper x || isLower x

||| Returns true if the character is in the range [0-9].
public export
isDigit : Char -> Bool
isDigit x = (x >= '0' && x <= '9')

||| Returns true if the character is in the ranges [A-Z][a-z][0-9].
public export
isAlphaNum : Char -> Bool
isAlphaNum x = isDigit x || isAlpha x

||| Returns true if the character is a whitespace character.
public export
isSpace : Char -> Bool
isSpace x
    = x == ' '  || x == '\t' || x == '\r' ||
      x == '\n' || x == '\f' || x == '\v' ||
      x == '\xa0'

||| Returns true if the character represents a new line.
public export
isNL : Char -> Bool
isNL x = x == '\r' || x == '\n'

||| Convert a letter to the corresponding upper-case letter, if any.
||| Non-letters are ignored.
public export
toUpper : Char -> Char
toUpper x
    = if (isLower x)
         then prim__cast_IntChar (prim__cast_CharInt x - 32)
         else x

||| Convert a letter to the corresponding lower-case letter, if any.
||| Non-letters are ignored.
public export
toLower : Char -> Char
toLower x
    = if (isUpper x)
         then prim__cast_IntChar (prim__cast_CharInt x + 32)
         else x

||| Returns true if the character is a hexadecimal digit i.e. in the range
||| [0-9][a-f][A-F].
public export
isHexDigit : Char -> Bool
isHexDigit x = elem (toUpper x) hexChars where
  hexChars : List Char
  hexChars
      = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
         'A', 'B', 'C', 'D', 'E', 'F']

||| Returns true if the character is an octal digit.
public export
isOctDigit : Char -> Bool
isOctDigit x = (x >= '0' && x <= '7')

||| Returns true if the character is a control character.
public export
isControl : Char -> Bool
isControl x
    = (x >= '\x0000' && x <= '\x001f')
       || (x >= '\x007f' && x <= '\x009f')

||| Convert the number to its backend dependent (usually Unicode) Char
||| equivalent.
public export
chr : Int -> Char
chr = prim__cast_IntChar

||| Return the backend dependent (usually Unicode) numerical equivalent of the Char.
public export
ord : Char -> Int
ord = prim__cast_CharInt

-----------------------
-- DOUBLE PRIMITIVES --
-----------------------

public export
pi : Double
pi = 3.14159265358979323846

public export
euler : Double
euler = 2.7182818284590452354

public export
exp : Double -> Double
exp x = prim__doubleExp x

public export
log : Double -> Double
log x = prim__doubleLog x

public export
pow : Double -> Double -> Double
pow x y = exp (y * log x)

public export
sin : Double -> Double
sin x = prim__doubleSin x

public export
cos : Double -> Double
cos x = prim__doubleCos x

public export
tan : Double -> Double
tan x = prim__doubleTan x

public export
asin : Double -> Double
asin x = prim__doubleASin x

public export
acos : Double -> Double
acos x = prim__doubleACos x

public export
atan : Double -> Double
atan x = prim__doubleATan x

public export
sinh : Double -> Double
sinh x = (exp x - exp (-x)) / 2

public export
cosh : Double -> Double
cosh x = (exp x + exp (-x)) / 2

public export
tanh : Double -> Double
tanh x = sinh x / cosh x

public export
sqrt : Double -> Double
sqrt x = prim__doubleSqrt x

public export
floor : Double -> Double
floor x = prim__doubleFloor x

public export
ceiling : Double -> Double
ceiling x = prim__doubleCeiling x

-----------
-- CASTS --
-----------

-- Casts between primitives only here.  They might be lossy.

||| Interface for transforming an instance of a data type to another type.
public export
interface Cast from to where
  ||| Perform a (potentially lossy!) cast operation.
  ||| @ orig The original type
  cast : (orig : from) -> to

-- To String

export
Cast Int String where
  cast = prim__cast_IntString

export
Cast Integer String where
  cast = prim__cast_IntegerString

export
Cast Char String where
  cast = prim__cast_CharString

export
Cast Double String where
  cast = prim__cast_DoubleString

-- To Integer

export
Cast Int Integer where
  cast = prim__cast_IntInteger

export
Cast Char Integer where
  cast = prim__cast_CharInteger

export
Cast Double Integer where
  cast = prim__cast_DoubleInteger

export
Cast String Integer where
  cast = prim__cast_StringInteger

export
Cast Nat Integer where
  cast = natToInteger

export
Cast Bits8 Integer where
  cast = prim__cast_Bits8Integer

export
Cast Bits16 Integer where
  cast = prim__cast_Bits16Integer

export
Cast Bits32 Integer where
  cast = prim__cast_Bits32Integer

export
Cast Bits64 Integer where
  cast = prim__cast_Bits64Integer

-- To Int

export
Cast Integer Int where
  cast = prim__cast_IntegerInt

export
Cast Char Int where
  cast = prim__cast_CharInt

export
Cast Double Int where
  cast = prim__cast_DoubleInt

export
Cast String Int where
  cast = prim__cast_StringInt

export
Cast Nat Int where
  cast = fromInteger . natToInteger

export
Cast Bits8 Int where
  cast = prim__cast_Bits8Int

export
Cast Bits16 Int where
  cast = prim__cast_Bits16Int

export
Cast Bits32 Int where
  cast = prim__cast_Bits32Int

export
Cast Bits64 Int where
  cast = prim__cast_Bits64Int

-- To Char

export
Cast Int Char where
  cast = prim__cast_IntChar

-- To Double

export
Cast Int Double where
  cast = prim__cast_IntDouble

export
Cast Integer Double where
  cast = prim__cast_IntegerDouble

export
Cast String Double where
  cast = prim__cast_StringDouble

export
Cast Nat Double where
  cast = prim__cast_IntegerDouble . natToInteger


-- To Bits8

export
Cast Int Bits8 where
  cast = prim__cast_IntBits8

export
Cast Integer Bits8 where
  cast = prim__cast_IntegerBits8

export
Cast Bits16 Bits8 where
  cast = prim__cast_Bits16Bits8

export
Cast Bits32 Bits8 where
  cast = prim__cast_Bits32Bits8

export
Cast Bits64 Bits8 where
  cast = prim__cast_Bits64Bits8


-- To Bits16

export
Cast Int Bits16 where
  cast = prim__cast_IntBits16

export
Cast Integer Bits16 where
  cast = prim__cast_IntegerBits16

export
Cast Bits8 Bits16 where
  cast = prim__cast_Bits8Bits16

export
Cast Bits32 Bits16 where
  cast = prim__cast_Bits32Bits16

export
Cast Bits64 Bits16 where
  cast = prim__cast_Bits64Bits16


-- To Bits32

export
Cast Int Bits32 where
  cast = prim__cast_IntBits32

export
Cast Integer Bits32 where
  cast = prim__cast_IntegerBits32

export
Cast Bits8 Bits32 where
  cast = prim__cast_Bits8Bits32

export
Cast Bits16 Bits32 where
  cast = prim__cast_Bits16Bits32

export
Cast Bits64 Bits32 where
  cast = prim__cast_Bits64Bits32

-- To Bits64

export
Cast Int Bits64 where
  cast = prim__cast_IntBits64

export
Cast Integer Bits64 where
  cast = prim__cast_IntegerBits64

export
Cast Bits8 Bits64 where
  cast = prim__cast_Bits8Bits64

export
Cast Bits16 Bits64 where
  cast = prim__cast_Bits16Bits64

export
Cast Bits32 Bits64 where
  cast = prim__cast_Bits32Bits64


------------
-- RANGES --
------------

public export
countFrom : n -> (n -> n) -> Stream n
countFrom start diff = start :: countFrom (diff start) diff

-- this and takeBefore are for range syntax, and not exported here since
-- they're partial. They are exported from Data.Stream instead.
partial
takeUntil : (n -> Bool) -> Stream n -> List n
takeUntil p (x :: xs)
    = if p x
         then [x]
         else x :: takeUntil p xs

partial
takeBefore : (n -> Bool) -> Stream n -> List n
takeBefore p (x :: xs)
    = if p x
         then []
         else x :: takeBefore p xs

public export
interface Range a where
  rangeFromTo : a -> a -> List a
  rangeFromThenTo : a -> a -> a -> List a

  rangeFrom : a -> Stream a
  rangeFromThen : a -> a -> Stream a

-- Idris 1 went to great lengths to prove that these were total. I don't really
-- think it's worth going to those lengths! Let's keep it simple and assert.
export
Range Nat where
  rangeFromTo x y
      = if y > x
           then assert_total $ takeUntil (>= y) (countFrom x S)
           else if x > y
                   then assert_total $ takeUntil (<= y) (countFrom x (\n => minus n 1))
                   else [x]
  rangeFromThenTo x y z
      = if y > x
           then (if z > x
                    then assert_total $ takeBefore (> z) (countFrom x (plus (minus y x)))
                    else [])
           else (if x == y
                    then (if x == z then [x] else [])
                    else assert_total $ takeBefore (< z) (countFrom x (\n => minus n (minus x y))))
  rangeFrom x = countFrom x S
  rangeFromThen x y
      = if y > x
           then countFrom x (plus (minus y x))
           else countFrom x (\n => minus n (minus x y))

export
(Integral a, Ord a, Neg a) => Range a where
  rangeFromTo x y
      = if y > x
           then assert_total $ takeUntil (>= y) (countFrom x (+1))
           else if x > y
                   then assert_total $ takeUntil (<= y) (countFrom x (\x => x-1))
                   else [x]
  rangeFromThenTo x y z
      = if (z - x) > (z - y)
           then -- go up
             assert_total $ takeBefore (> z) (countFrom x (+ (y-x)))
           else if (z - x) < (z - y)
                then -- go down
                     assert_total $ takeBefore (< z) (countFrom x (\n => n - (x - y)))
                else -- meaningless
                  if x == y && y == z
                     then [x] else []
  rangeFrom x = countFrom x (1+)
  rangeFromThen x y
      = if y > x
           then countFrom x (+ (y - x))
           else countFrom x (\n => n - (x - y))
