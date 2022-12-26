module Prelude.Types

import Builtin
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

-- This is used in the compiler as an efficient substitute for integerToNat.
prim__integerToNat : Integer -> Nat
prim__integerToNat i
  = if intToBool (prim__lte_Integer 0 i)
      then believe_me i
      else Z

public export
integerToNat : Integer -> Nat
integerToNat 0 = Z -- Force evaluation and hence caching of x at compile time
integerToNat x
  = if intToBool (prim__lte_Integer x 0)
       then Z
       else S (assert_total (integerToNat (prim__sub_Integer x 1)))

-- %builtin IntegerToNatural Prelude.Types.integerToNat

-- Define separately so we can spot the name when optimising Nats
||| Add two natural numbers.
||| @ x the number to case-split on
||| @ y the other numberpublic export
public export
plus : (x : Nat) -> (y : Nat) -> Nat
plus Z y = y
plus (S k) y = S (plus k y)

||| Subtract natural numbers.  If the second number is larger than the first,
||| return 0.
public export
minus : (left : Nat) -> Nat -> Nat
minus Z        right     = Z
minus left     Z         = left
minus (S left) (S right) = minus left right

||| Multiply natural numbers.
public export
mult : (x : Nat) -> Nat -> Nat
mult Z y = Z
mult (S k) y = plus y (mult k y)

public export
Num Nat where
  (+) = plus
  (*) = mult

  fromInteger x = integerToNat x

-- used for nat hack
public export
equalNat : (m, n : Nat) -> Bool
equalNat Z Z = True
equalNat (S j) (S k) = equalNat j k
equalNat _ _ = False

public export
Eq Nat where
  (==) = equalNat

-- used for nat hack
public export
compareNat : (m, n : Nat) -> Ordering
compareNat Z Z = EQ
compareNat Z (S k) = LT
compareNat (S k) Z = GT
compareNat (S j) (S k) = compareNat j k

public export
Ord Nat where
  compare = compareNat

public export
natToInteger : Nat -> Integer
natToInteger Z = 0
natToInteger (S k) = 1 + natToInteger k
                         -- integer (+) may be non-linear in second
                         -- argument

-- %builtin NaturalToInteger Prelude.Types.natToInteger

||| Counts the number of elements that satify a predicate.
public export
count : Foldable t => (predicate : a -> Bool) -> t a -> Nat
count predicate = foldMap @{%search} @{Additive} (\x => if predicate x then 1 else 0)

-----------
-- PAIRS --
-----------

%inline
public export
Bifunctor Pair where
  bimap f g (x, y) = (f x, g y)

%inline
public export
Bifoldable Pair where
  bifoldr f g acc (x, y) = f x (g y acc)
  bifoldl f g acc (x, y) = g (f acc x) y
  binull _ = False

%inline
public export
Bitraversable Pair where
  bitraverse f g (a,b) = [| (,) (f a) (g b) |]

%inline
public export
Functor (Pair a) where
  map = mapSnd

%inline
public export
Foldable (Pair a) where
  foldr op init (_, x) = x `op` init
  foldl op init (_, x) = init `op` x
  null _ = False

%inline
public export
Traversable (Pair a) where
  traverse f (l, r) = (l,) <$> f r

%inline
public export
Monoid a => Applicative (Pair a) where
  pure = (neutral,)
  (a1,f) <*> (a2,v) = (a1 <+> a2, f v)

%inline
public export
Monoid a => Monad (Pair a) where
  (a1,a) >>= f = let (a2,b) = f a in (a1 <+> a2, b)

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
  Just : (x : ty) -> Maybe ty

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

||| Execute an applicative expression when the Maybe is Just
%inline public export
whenJust : Applicative f => Maybe a -> (a -> f ()) -> f ()
whenJust (Just a) k = k a
whenJust Nothing k = pure ()

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
  _      <*> _      = Nothing

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
  null Nothing = True
  null (Just _) = False

public export
Traversable Maybe where
  traverse f Nothing = pure Nothing
  traverse f (Just x) = Just <$> f x

-----------------
-- EQUIVALENCE --
-----------------

public export
record (<=>) (a, b : Type) where
  constructor MkEquivalence
  leftToRight : a -> b
  rightToLeft : b -> a

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
  No  : (contra : Not prop) -> Dec prop

export Uninhabited (Yes p === No q) where uninhabited eq impossible
export Uninhabited (No p === Yes q) where uninhabited eq impossible

public export
viaEquivalence : a <=> b -> Dec a -> Dec b
viaEquivalence f (Yes a) = Yes (f .leftToRight a)
viaEquivalence f (No na) = No (na . f .rightToLeft)

------------
-- EITHER --
------------

||| A sum type.
public export
data Either : (a : Type) -> (b : Type) -> Type where
  ||| One possibility of the sum, conventionally used to represent errors.
  Left : forall a, b. (x : a) -> Either a b

  ||| The other possibility, conventionally used to represent success.
  Right : forall a, b. (x : b) -> Either a b

export Uninhabited (Left p === Right q) where uninhabited eq impossible
export Uninhabited (Right p === Left q) where uninhabited eq impossible

export
Either (Uninhabited a) (Uninhabited b) => Uninhabited (a, b) where
  uninhabited (x, _) @{Left  _} = uninhabited x
  uninhabited (_, y) @{Right _} = uninhabited y

export
Uninhabited a => Uninhabited b => Uninhabited (Either a b) where
  uninhabited (Left l)  = uninhabited l
  uninhabited (Right r) = uninhabited r

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
Bifoldable Either where
  bifoldr f _ acc (Left a)  = f a acc
  bifoldr _ g acc (Right b) = g b acc

  bifoldl f _ acc (Left a)  = f acc a
  bifoldl _ g acc (Right b) = g acc b

  binull _ = False

%inline
public export
Bitraversable Either where
  bitraverse f _ (Left a)  = Left <$> f a
  bitraverse _ g (Right b) = Right <$> g b

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
  null (Left _) = True
  null (Right _) = False

public export
Traversable (Either e) where
  traverse f (Left x)  = pure (Left x)
  traverse f (Right x) = Right <$> f x

-----------
-- LISTS --
-----------

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

namespace SnocList

  infixl 7 <><
  infixr 6 <>>

  ||| 'fish': Action of lists on snoc-lists
  public export
  (<><) : SnocList a -> List a -> SnocList a
  sx <>< [] = sx
  sx <>< (x :: xs) = sx :< x <>< xs

  ||| 'chips': Action of snoc-lists on lists
  public export
  (<>>) : SnocList a -> List a -> List a
  Lin       <>> xs = xs
  (sx :< x) <>> xs = sx <>> x :: xs

  public export
  (++) : (sx, sy : SnocList a) -> SnocList a
  (++) sx Lin = sx
  (++) sx (sy :< y) = (sx ++ sy) :< y

  public export
  length : SnocList a -> Nat
  length Lin = Z
  length (sx :< x) = S $ length sx

  ||| Filters a snoc-list according to a simple classifying function
  public export
  filter : (a -> Bool) -> SnocList a -> SnocList a
  filter f [<]     = [<]
  filter f (xs:<x) = let rest = filter f xs in if f x then rest :< x else rest

  ||| Apply a partial function to the elements of a list, keeping the ones at which
  ||| it is defined.
  public export
  mapMaybe : (a -> Maybe b) -> SnocList a -> SnocList b
  mapMaybe f [<]       = [<]
  mapMaybe f (sx :< x) = case f x of
    Nothing => mapMaybe f sx
    Just j  => mapMaybe f sx :< j

  ||| Reverse the second snoclist, prepending its elements to the first.
  public export
  reverseOnto : SnocList a -> SnocList a -> SnocList a
  reverseOnto acc Lin       = acc
  reverseOnto acc (sx :< x) = reverseOnto (acc :< x) sx

  ||| Reverses the given list.
  public export
  reverse : SnocList a -> SnocList a
  reverse = reverseOnto Lin

  ||| Tail-recursive append. Uses of (++) are automatically transformed to
  ||| this. The only reason this is exported is that the proof of equivalence
  ||| lives in a different module.
  public export
  tailRecAppend : (sx, sy : SnocList a) -> SnocList a
  tailRecAppend sx sy = reverseOnto sx (reverse sy)

  -- Always use tailRecAppend at runtime. Data.SnocList.tailRecAppendIsAppend
  -- proves these are equivalent.
  %transform "tailRecAppendSnocList" SnocList.(++) = SnocList.tailRecAppend

  ||| Returns the first argument plus the length of the second.
  public export
  lengthPlus : Nat -> SnocList a -> Nat
  lengthPlus n Lin       = n
  lengthPlus n (sx :< _) = lengthPlus (S n) sx

  ||| `length` implementation that uses tail recursion. Exported so
  ||| lengthTRIsLength can see it.
  public export
  lengthTR : SnocList a -> Nat
  lengthTR = lengthPlus Z

  -- Data.List.lengthTRIsLength proves these are equivalent.
  %transform "tailRecLengthSnocList" SnocList.length = SnocList.lengthTR

  ||| Utility for implementing `mapMaybeTR`
  public export
  mapMaybeAppend : List b -> (a -> Maybe b) -> SnocList a -> SnocList b
  mapMaybeAppend xs f (sx :< x) = case f x of
    Just v  => mapMaybeAppend (v :: xs) f sx
    Nothing => mapMaybeAppend xs f sx
  mapMaybeAppend xs f Lin       = Lin <>< xs

  ||| Tail recursive version of `mapMaybe`. This is automatically used
  ||| at runtime due to a `transform` rule.
  public export %inline
  mapMaybeTR : (a -> Maybe b) -> SnocList a -> SnocList b
  mapMaybeTR = mapMaybeAppend []

  -- Data.List.mapMaybeTRIsMapMaybe proves these are equivalent.
  %transform "tailRecMapMaybeSnocList" SnocList.mapMaybe = SnocList.mapMaybeTR

  ||| Utility for implementing `filterTR`
  public export
  filterAppend : List a -> (a -> Bool) -> SnocList a -> SnocList a
  filterAppend xs f (sx :< x) = case f x of
    True  => filterAppend (x :: xs) f sx
    False => filterAppend xs f sx
  filterAppend xs f Lin       = Lin <>< xs

  ||| Tail recursive version of `filter`. This is automatically used
  ||| at runtime due to a `transform` rule.
  public export %inline
  filterTR : (a -> Bool) -> SnocList a -> SnocList a
  filterTR = filterAppend []

  -- Data.List.listTRIsList proves these are equivalent.
  %transform "tailRecFilterSnocList" SnocList.filter = SnocList.filterTR

namespace List

  ||| Concatenate one list with another.
  public export
  (++) : (xs, ys : List a) -> List a
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: xs ++ ys

  ||| Returns the length of the list.
  public export
  length : List a -> Nat
  length []        = Z
  length (x :: xs) = S (length xs)

  ||| Applied to a predicate and a list, returns the list of those elements that
  ||| satisfy the predicate.
  public export
  filter : (p : a -> Bool) -> List a -> List a
  filter p [] = []
  filter p (x :: xs)
     = if p x
          then x :: filter p xs
          else filter p xs

  ||| Apply a partial function to the elements of a list, keeping the ones at which it is defined.
  public export
  mapMaybe : (a -> Maybe b) -> List a -> List b
  mapMaybe f []      = []
  mapMaybe f (x::xs) =
    case f x of
      Nothing => mapMaybe f xs
      Just j  => j :: mapMaybe f xs

  ||| Reverse the second list, prepending its elements to the first.
  public export
  reverseOnto : List a -> List a -> List a
  reverseOnto acc [] = acc
  reverseOnto acc (x::xs) = reverseOnto (x::acc) xs

  ||| Reverses the given list.
  public export
  reverse : List a -> List a
  reverse = reverseOnto []

  ||| Tail-recursive append. Uses of (++) are automatically transformed to
  ||| this. The only reason this is exported is that the proof of equivalence
  ||| lives in a different module.
  public export
  tailRecAppend : (xs, ys : List a) -> List a
  tailRecAppend xs ys = reverseOnto ys (reverse xs)

  -- Always use tailRecAppend at runtime. Data.List.tailRecAppendIsAppend
  -- proves these are equivalent.
  %transform "tailRecAppend" List.(++) = List.tailRecAppend

  ||| Returns the first argument plus the length of the second.
  public export
  lengthPlus : Nat -> List a -> Nat
  lengthPlus n [] = n
  lengthPlus n (x::xs) = lengthPlus (S n) xs

  ||| `length` implementation that uses tail recursion. Exported so
  ||| lengthTRIsLength can see it.
  public export
  lengthTR : List a -> Nat
  lengthTR = lengthPlus Z

  -- Data.List.lengthTRIsLength proves these are equivalent.
  %transform "tailRecLength" List.length = List.lengthTR

  public export
  mapImpl : (a -> b) -> List a -> List b
  mapImpl f [] = []
  mapImpl f (x :: xs) = f x :: mapImpl f xs

  ||| Utility for implementing `mapTR`
  public export
  mapAppend : SnocList b -> (a -> b) -> List a -> List b
  mapAppend sx f (x :: xs) = mapAppend (sx :< f x) f xs
  mapAppend sx f []        = sx <>> []

  ||| Tail recursive version of `map`. This is automatically used
  ||| at runtime due to a `transform` rule.
  public export %inline
  mapTR : (a -> b) -> List a -> List b
  mapTR = mapAppend Lin

  -- Data.List.mapTRIsMap proves these are equivalent.
  %transform "tailRecMap" mapImpl = List.mapTR

  ||| Utility for implementing `mapMaybeTR`
  public export
  mapMaybeAppend : SnocList b -> (a -> Maybe b) -> List a -> List b
  mapMaybeAppend sx f (x :: xs) = case f x of
    Just v  => mapMaybeAppend (sx :< v) f xs
    Nothing => mapMaybeAppend sx f xs
  mapMaybeAppend sx f []        = sx <>> []

  ||| Tail recursive version of `mapMaybe`. This is automatically used
  ||| at runtime due to a `transform` rule.
  public export %inline
  mapMaybeTR : (a -> Maybe b) -> List a -> List b
  mapMaybeTR = mapMaybeAppend Lin

  -- Data.List.mapMaybeTRIsMapMaybe proves these are equivalent.
  %transform "tailRecMapMaybe" List.mapMaybe = List.mapMaybeTR

  ||| Utility for implementing `filterTR`
  public export
  filterAppend : SnocList a -> (a -> Bool) -> List a -> List a
  filterAppend sx f (x :: xs) = case f x of
    True  => filterAppend (sx :< x) f xs
    False => filterAppend sx f xs
  filterAppend sx f []        = sx <>> []

  ||| Tail recursive version of `filter`. This is automatically used
  ||| at runtime due to a `transform` rule.
  public export %inline
  filterTR : (a -> Bool) -> List a -> List a
  filterTR = filterAppend Lin

  -- Data.List.listTRIsList proves these are equivalent.
  %transform "tailRecFilter" List.filter = List.filterTR

public export %inline
Functor List where
  map = mapImpl

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

  null [] = True
  null (_::_) = False

  toList = id

  foldMap f = foldl (\acc, elem => acc <+> f elem) neutral

public export
listBindOnto : (a -> List b) -> List b -> List a -> List b
listBindOnto f xs []        = reverse xs
listBindOnto f xs (y :: ys) = listBindOnto f (reverseOnto xs (f y)) ys

-- tail recursive O(n) implementation of `(>>=)` for `List`
public export
listBind : List a -> (a -> List b) -> List b
listBind as f = listBindOnto f Nil as

public export
Applicative List where
  pure x = [x]
  fs <*> vs = listBind fs (\f => map f vs)

public export
Alternative List where
  empty = []
  xs <|> ys = xs ++ ys

public export
Monad List where
  (>>=) = listBind

public export
Traversable List where
  traverse f [] = pure []
  traverse f (x::xs) = [| f x :: traverse f xs |]

public export
Eq a => Eq (SnocList a) where
  (==) Lin Lin = True
  (==) (sx :< x) (sy :< y) = x == y && sx == sy
  (==) _ _ = False

public export
Ord a => Ord (SnocList a) where
  compare Lin Lin = EQ
  compare Lin (sx :< x) = LT
  compare (sx :< x) Lin = GT
  compare (sx :< x) (sy :< y)
    = case compare sx sy of
        EQ => compare x y
        c  => c

-- This works quickly because when string-concat builds the result, it allocates
-- enough room in advance so there's only one allocation, rather than lots!
--
-- Like fastUnpack, this function won't reduce at compile time.
-- If you need to concatenate strings at compile time, use Prelude.concat.
%foreign
  "scheme:string-concat"
  "RefC:fastConcat"
  "javascript:lambda:(xs)=>__prim_idris2js_array(xs).join('')"
export
fastConcat : List String -> String

%transform "fastConcat" concat {t = List} {a = String} = fastConcat

||| Check if something is a member of a list using a custom comparison.
public export
elemBy : Foldable t => (a -> a -> Bool) -> a -> t a -> Bool
elemBy p e = any (p e)

||| Check if something is a member of a list using the default Boolean equality.
public export
elem : Foldable t => Eq a => a -> t a -> Bool
elem = elemBy (==)

||| Lookup a value at a given position
export
getAt : Nat -> List a -> Maybe a
getAt Z     (x :: xs) = Just x
getAt (S k) (x :: xs) = getAt k xs
getAt _     []        = Nothing

-------------
-- STREAMS --
-------------

namespace Stream
  ||| An infinite stream.
  public export
  data Stream : Type -> Type where
       (::) : a -> Inf (Stream a) -> Stream a

%name Stream xs, ys, zs

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
take : (n : Nat) -> (xs : Stream a) -> List a
take Z xs = []
take (S k) (x :: xs) = x :: take k xs

-------------
-- STRINGS --
-------------

namespace String
  public export
  (++) : (x : String) -> (y : String) -> String
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
    "RefC:fastPack"
    "javascript:lambda:(xs)=>__prim_idris2js_array(xs).join('')"
export
fastPack : List Char -> String

-- always use 'fastPack' at run time
%transform "fastPack" pack = fastPack

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
             else unpack' (assert_smaller pos (pos - 1)) str $ (assert_total $ prim__strIndex str pos) :: acc

-- This function runs fast when compiled but won't compute at compile time.
-- If you need to unpack strings at compile time, use Prelude.unpack.
%foreign
  "scheme:string-unpack"
  "RefC:fastUnpack"
  "javascript:lambda:(str)=>__prim_js2idris_array(Array.from(str))"
export
fastUnpack : String -> List Char

-- always use 'fastPack' at run time
%transform "fastUnpack" unpack = fastUnpack

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
isSpace ' '    = True
isSpace '\t'   = True
isSpace '\r'   = True
isSpace '\n'   = True
isSpace '\f'   = True
isSpace '\v'   = True
isSpace '\xa0' = True
isSpace _      = False

||| Returns true if the character represents a new line.
public export
isNL : Char -> Bool
isNL '\r' = True
isNL '\n' = True
isNL _    = False

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
isHexDigit x = isDigit x || ('a' <= x && x <= 'f') || ('A' <= x && x <= 'F')

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
pow x y = prim__doublePow x y

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

------------
-- RANGES --
------------

-- These functions are here to support the range syntax:
-- range expressions like `[a..b]` are desugared to `rangeFromXXX` calls.

public export
countFrom : n -> (n -> n) -> Stream n
countFrom start diff = start :: countFrom (diff start) diff

public export
covering
takeUntil : (n -> Bool) -> Stream n -> List n
takeUntil p (x :: xs)
    = if p x
         then [x]
         else x :: takeUntil p xs

public export
covering
takeBefore : (n -> Bool) -> Stream n -> List n
takeBefore p (x :: xs)
    = if p x
         then []
         else x :: takeBefore p xs

public export
interface Range a where
  constructor MkRange
  rangeFromTo : a -> a -> List a
  rangeFromThenTo : a -> a -> a -> List a

  rangeFrom : a -> Stream a
  rangeFromThen : a -> a -> Stream a

-- Idris 1 went to great lengths to prove that these were total. I don't really
-- think it's worth going to those lengths! Let's keep it simple and assert.
public export
Range Nat where
  rangeFromTo x y = case compare x y of
    LT => assert_total $ takeUntil (>= y) (countFrom x S)
    EQ => pure x
    GT => assert_total $ takeUntil (<= y) (countFrom x (\n => minus n 1))
  rangeFromThenTo x y z = case compare x y of
    LT => if z >= x
             then assert_total $ takeBefore (> z) (countFrom x (plus (minus y x)))
             else Nil
    EQ => if x == z then pure x else Nil
    GT => assert_total $ takeBefore (< z) (countFrom x (\n => minus n (minus x y)))
  rangeFrom x = countFrom x S
  rangeFromThen x y
      = if y > x
           then countFrom x (plus (minus y x))
           else countFrom x (\n => minus n (minus x y))

public export
(Integral a, Ord a, Neg a) => Range a where
  rangeFromTo x y = case compare x y of
    LT => assert_total $ takeUntil (>= y) (countFrom x (+1))
    EQ => pure x
    GT => assert_total $ takeUntil (<= y) (countFrom x (\x => x-1))
  rangeFromThenTo x y z = case compare (z - x) (z - y) of
    -- Go down
    LT => assert_total $ takeBefore (< z) (countFrom x (\n => n - (x - y)))
    -- Meaningless
    EQ => if x == y && y == z then pure x else Nil
    -- Go up
    GT => assert_total $ takeBefore (> z) (countFrom x (+ (y-x)))
  rangeFrom x = countFrom x (1+)
  rangeFromThen x y
      = if y > x
           then countFrom x (+ (y - x))
           else countFrom x (\n => n - (x - y))

public export
Range Char where
  rangeFromTo x y = map chr $ rangeFromTo (ord x) (ord y)
  rangeFromThenTo x y z = map chr $ rangeFromThenTo (ord x) (ord y) (ord z)
  rangeFrom x = map chr $ rangeFrom (ord x)
  rangeFromThen x y = map chr $ rangeFromThen (ord x) (ord y)
