module Core.Name.ScopedList

import Data.Nat
import Data.SnocList
import Data.Vect
import Core.Name

import public Data.Zippable

import Libraries.Data.IntMap

%default total

mutual
  export infixr 7 :%:

  public export
  data ScopedList a = Lin | (:%:) a (ScopedList a)
  -- TODO: make that a SnocList

export infixr 7 +%+

public export
length : ScopedList a -> Nat
length [<]        = Z
length (x :%: xs) = S (length xs)

public export
take : (n : Nat) -> (xs : ScopedList a) -> ScopedList a
take (S k) (x :%: xs) = x :%: take k xs
take _ _ = [<]

public export
mapImpl : (a -> b) -> ScopedList a -> ScopedList b
mapImpl f [<] = [<]
mapImpl f (x :%: xs) = (f x) :%: (mapImpl f xs)

public export %inline
Functor ScopedList where
  map = mapImpl

export
lengthMap : (xs : ScopedList a) -> length (mapImpl f xs) = length xs
lengthMap [<] = Refl
lengthMap (x :%: xs) = cong S (lengthMap xs)

public export
Zippable ScopedList where
  zipWith _ [<] _ = [<]
  zipWith _ _ [<] = [<]
  zipWith f (x :%: xs) (y :%: ys) = f x y :%: zipWith f xs ys

  zipWith3 _ [<] _ _ = [<]
  zipWith3 _ _ [<] _ = [<]
  zipWith3 _ _ _ [<] = [<]
  zipWith3 f (x :%: xs) (y :%: ys) (z :%: zs) = f x y z :%: zipWith3 f xs ys zs

  unzipWith f [<] = ([<], [<])
  unzipWith f (x :%: xs) = let (b, c) = f x
                               (bs, cs) = unzipWith f xs in
                               (b :%: bs, c :%: cs)

  unzipWith3 f [<] = ([<], [<], [<])
  unzipWith3 f (x :%: xs) = let (b, c, d) = f x
                                (bs, cs, ds) = unzipWith3 f xs in
                                (b :%: bs, c :%: cs, d :%: ds)

public export
(+%+) : (xs, ys : ScopedList a) -> ScopedList a
(+%+) [<] ys = ys
(+%+) (x :%: xs) ys = x :%: ((+%+) xs ys)

public export
Semigroup (ScopedList a) where
  (<+>) = (+%+)

public export
Monoid (ScopedList a) where
  neutral = [<]

public export
Foldable ScopedList where
  foldr c n [<] = n
  foldr c n (x :%: xs) = c x (foldr c n xs)

  foldl f q [<] = q
  foldl f q (x :%: xs) = foldl f (f q x) xs

  null [<] = True
  null (_ :%: _) = False

  toList [<] = []
  toList (a :%: ax) = a :: toList ax

  foldMap f = foldl (\acc, elem => acc <+> f elem) neutral

||| Find the first element of the list that satisfies the predicate.
public export
fromList : List a -> ScopedList a
fromList [] = [<]
fromList (a :: ax) = a :%: fromList ax

public export
data Thin : ScopedList a -> ScopedList a -> Type where
  Refl : Thin xs xs
  Drop : Thin xs ys -> Thin xs (y :%: ys)
  Keep : Thin xs ys -> Thin (x :%: xs) (x :%: ys)

export
keeps : (args : ScopedList a) -> Thin xs ys -> Thin (args +%+ xs) (args +%+ ys)
keeps [<] th = th
keeps (x :%: xs) th = Keep (keeps xs th)

||| Ensure that the list's length is the provided natural number
public export
data HasLength : Nat -> ScopedList a -> Type where
  Z : HasLength Z [<]
  S : HasLength n xs -> HasLength (S n) (x :%: xs)

export
hasLengthAppend : HasLength m xs -> HasLength n ys -> HasLength (m + n) (xs +%+ ys)
hasLengthAppend Z ys = ys
hasLengthAppend (S xs) ys = S (hasLengthAppend xs ys)

export
mkHasLength : (xs : ScopedList a) -> HasLength (length xs) xs
mkHasLength [<] = Z
mkHasLength (_ :%: xs) = S (mkHasLength xs)

public export
record SizeOf {a : Type} (xs : ScopedList a) where
  constructor MkSizeOf
  size        : Nat
  0 hasLength : HasLength size xs

public export
zero : SizeOf [<]
zero = MkSizeOf Z Z

public export
suc : SizeOf as -> SizeOf (a :%: as)
suc (MkSizeOf n p) = MkSizeOf (S n) (S p)

public export
snoc : ScopedList a -> a -> ScopedList a
snoc xs x = xs +%+ (x :%: [<])

namespace Stream
  public export
  take : (n : Nat) -> (xs : Stream a) -> ScopedList a
  take Z xs = [<]
  take (S k) (x :: xs) = x :%: take k xs

namespace HasLength
  export
  cast : {ys : _} -> (0 _ : Core.Name.ScopedList.length xs = Core.Name.ScopedList.length ys) -> HasLength m xs -> HasLength m ys
  cast {ys = [<]}      eq Z = Z
  cast {ys = y :%: ys} eq (S p) = S (cast (injective eq) p)

  export
  take : (n : Nat) -> (xs : Stream a) -> HasLength n (take n xs)
  take Z _ = Z
  take (S n) (x :: xs) = S (take n xs)

  export
  sucR : HasLength n xs -> HasLength (S n) (snoc xs x)
  sucR Z = S Z
  sucR (S n) = S (sucR n)

namespace SizeOf
  export
  take : {n : Nat} -> {0 sx : Stream a} -> SizeOf (take n sx)
  take = MkSizeOf n (Core.Name.ScopedList.HasLength.take n sx)

  export
  sucR : SizeOf as -> SizeOf (as +%+ (a :%: [<]))
  sucR (MkSizeOf n p) = MkSizeOf (S n) (sucR p)

  export
  map : SizeOf xs -> SizeOf (mapImpl f xs)
  map (MkSizeOf n p) = MkSizeOf n (cast (sym $ lengthMap xs) p)

export
(+) : SizeOf xs -> SizeOf ys -> SizeOf (xs +%+ ys)
MkSizeOf m p + MkSizeOf n q = MkSizeOf (m + n) (hasLengthAppend p q)

export
mkSizeOf : (xs : ScopedList a) -> SizeOf xs
mkSizeOf xs = MkSizeOf (length xs) (mkHasLength xs)

public export
data CompatibleVars : (xs, ys : ScopedList a) -> Type where
   Pre : CompatibleVars xs xs
   Ext : CompatibleVars xs ys -> CompatibleVars (n :%: xs) (m :%: ys)

public export
(<>>) : SnocList a -> ScopedList a -> ScopedList a
Lin       <>> xs = xs
(sx :< x) <>> xs = sx <>> (x :%: xs)

public export
Cast (SnocList a) (ScopedList a) where
  cast sx = sx <>> [<]

||| 'fish': Action of lists on snoc-lists
public export
(<><) : SnocList a -> ScopedList a -> SnocList a
sx <>< [<] = sx
sx <>< (x :%: xs) = sx :< x <>< xs

public export
Cast (ScopedList a) (SnocList a) where
  cast xs = Lin <>< xs

||| Appending lists is associative.
export
appendAssociative : (l, c, r : ScopedList a) -> l +%+ (c +%+ r) = (l +%+ c) +%+ r
appendAssociative [<]      c r = Refl
appendAssociative (_ :%: xs) c r = rewrite appendAssociative xs c r in Refl

export
chipsAsListAppend : (xs : SnocList a) -> (ys : ScopedList a) -> xs <>> ys = cast xs +%+ ys
chipsAsListAppend [<]       ys = Refl
chipsAsListAppend (sx :< x) ys = do
  rewrite chipsAsListAppend sx (x :%: ys)
  rewrite chipsAsListAppend sx (x :%: [<])
  rewrite sym $ appendAssociative (cast sx) (x :%: [<]) ys
  Refl

public export
data Bounds : ScopedList Name -> Type where
      None : Bounds [<]
      Add : (x : Name) -> Name -> Bounds xs -> Bounds (x :%: xs)

export
sizeOf : Bounds xs -> SizeOf xs
sizeOf None        = zero
sizeOf (Add _ _ b) = suc (sizeOf b)

export
appendNilRightNeutral : (l : ScopedList a) -> l +%+ [<] = l
appendNilRightNeutral [<]      = Refl
appendNilRightNeutral (_ :%: xs) = rewrite appendNilRightNeutral xs in Refl

export
Show a => Show (ScopedList a) where
  show xs = "[%>" ++ show' "" xs ++ "<%]"
    where
      show' : String -> ScopedList a -> String
      show' acc [<]        = acc
      show' acc (x :%: [<])       = acc ++ show x
      show' acc (x :%: xs) = show' (acc ++ show x ++ ", ") xs


||| Reverse the second list, prepending its elements to the first.
public export
reverseOnto : ScopedList a -> ScopedList a -> ScopedList a
reverseOnto acc [<] = acc
reverseOnto acc (x:%:xs) = reverseOnto (x:%:acc) xs

||| Reverses the given list.
public export
reverse : ScopedList a -> ScopedList a
reverse = reverseOnto [<]

hasLengthReverseOnto : HasLength m acc -> HasLength n xs -> HasLength (m + n) (reverseOnto acc xs)
hasLengthReverseOnto p Z = rewrite plusZeroRightNeutral m in p
hasLengthReverseOnto {n = S n} p (S q) = rewrite sym (plusSuccRightSucc m n) in hasLengthReverseOnto (S p) q

export
hasLengthReverse : HasLength m acc -> HasLength m (reverse acc)
hasLengthReverse = hasLengthReverseOnto Z

||| Apply a partial function to the elements of a list, keeping the ones at which it is defined.
public export
mapMaybe : (a -> Maybe b) -> ScopedList a -> ScopedList b
mapMaybe f [<]      = [<]
mapMaybe f (x:%:xs) =
  case f x of
    Nothing => mapMaybe f xs
    Just j  => j :%: mapMaybe f xs

public export
listBindOnto : (a -> ScopedList b) -> ScopedList b -> ScopedList a -> ScopedList b
listBindOnto f xs [<]        = reverse xs
listBindOnto f xs (y :%: ys) = listBindOnto f (reverseOnto xs (f y)) ys

-- tail recursive O(n) implementation of `(>>=)` for `List`
public export
listBind : ScopedList a -> (a -> ScopedList b) -> ScopedList b
listBind as f = listBindOnto f [<] as

public export
Applicative ScopedList where
  pure x = (x :%: [<])
  fs <*> vs = listBind fs (\f => map f vs)

public export
Traversable ScopedList where
  traverse f [<] = pure [<]
  traverse f (x:%:xs) = [| f x :%: traverse f xs |]

||| List.length is distributive over appending.
export
lengthDistributesOverAppend : (xs, ys : ScopedList a) -> length (xs +%+ ys) = length xs + length ys
lengthDistributesOverAppend [<] ys = Refl
lengthDistributesOverAppend (x :%: xs) ys =
  cong S $ lengthDistributesOverAppend xs ys

||| Boolean check for whether the list is the empty list.
public export
isNil : ScopedList a -> Bool
isNil [<] = True
isNil _  = False

public export
toVect : (n : Nat) -> ScopedList a -> Maybe (Vect n a)
toVect Z [<] = Just []
toVect (S k) (x :%: xs)
    = do xs' <- toVect k xs
         pure (x :: xs')
toVect _ _ = Nothing

namespace SizedView

  public export
  data SizedView : SizeOf as -> Type where
    Z : SizedView (MkSizeOf Z Z)
    S : (n : SizeOf as) -> SizedView (suc {a} n)

export
sizedView : (p : SizeOf as) -> SizedView p
sizedView (MkSizeOf Z Z)         = Z
sizedView (MkSizeOf (S n) (S p)) = S (MkSizeOf n p)

||| Lookup a value at a given position
export
getAt : Nat -> ScopedList a -> Maybe a
getAt Z     (x :%: xs) = Just x
getAt (S k) (x :%: xs) = getAt k xs
getAt _     [<]        = Nothing

public export
drop : (n : Nat) -> (xs : ScopedList a) -> ScopedList a
drop Z     xs      = xs
drop (S n) [<]      = [<]
drop (S n) (_:%:xs) = drop n xs

public export
data LengthMatch : ScopedList a -> ScopedList b -> Type where
     NilMatch : LengthMatch [<] [<]
     ConsMatch : LengthMatch xs ys -> LengthMatch (x :%: xs) (y :%: ys)

export
checkLengthMatch : (xs : ScopedList a) -> (ys : ScopedList b) -> Maybe (LengthMatch xs ys)
checkLengthMatch [<] [<] = Just NilMatch
checkLengthMatch [<] (x :%: xs) = Nothing
checkLengthMatch (x :%: xs) [<] = Nothing
checkLengthMatch (x :%: xs) (y :%: ys)
    = Just (ConsMatch !(checkLengthMatch xs ys))

export
lengthsMatch : LengthMatch xs ys -> (length xs) = (length ys)
lengthsMatch NilMatch = Refl
lengthsMatch (ConsMatch x) = cong (S) (lengthsMatch x)

namespace IntMap
  export
  toScopedList : IntMap v -> ScopedList (Int, v)
  toScopedList = fromList . toList

public export
Eq a => Eq (ScopedList a) where
  [<] == [<] = True
  x :%: xs == y :%: ys = x == y && xs == ys
  _ == _ = False

public export
Ord a => Ord (ScopedList a) where
  compare [<] [<] = EQ
  compare [<] (x :%: xs) = LT
  compare (x :%: xs) [<] = GT
  compare (x :%: xs) (y :%: ys)
     = case compare x y of
            EQ => compare xs ys
            c => c

||| Find the first element of the list that satisfies the predicate.
public export
find : (p : a -> Bool) -> (xs : ScopedList a) -> Maybe a
find p [<] = Nothing
find p (x:%:xs) = if p x then Just x else find p xs

export
none : {xs : ScopedList a} -> Thin [<] xs
none {xs = [<]} = Refl
none {xs = _ :%: _} = Drop none
