module Data.Maybe

import Control.Function

import Data.Zippable

%default total

public export
isNothing : Maybe a -> Bool
isNothing Nothing  = True
isNothing (Just _) = False

public export
isJust : Maybe a -> Bool
isJust Nothing  = False
isJust (Just _) = True

||| Proof that some `Maybe` is actually `Just`
public export
data IsJust : Maybe a -> Type where
  ItIsJust : IsJust (Just x)

export
Uninhabited (IsJust Nothing) where
  uninhabited ItIsJust impossible

||| Decide whether a 'Maybe' is 'Just'
public export
isItJust : (v : Maybe a) -> Dec (IsJust v)
isItJust (Just _) = Yes ItIsJust
isItJust Nothing = No absurd

||| Convert a `Maybe a` value to an `a` value by providing a default `a` value
||| in the case that the `Maybe` value is `Nothing`.
public export
fromMaybe : (Lazy a) -> Maybe a -> a
fromMaybe def Nothing  = def
fromMaybe _   (Just j) = j

||| Returns the `a` value of a `Maybe a` which is proved `Just`.
public export
fromJust : (v : Maybe a) -> (0 _ : IsJust v) => a
fromJust (Just x) = x
fromJust Nothing impossible

||| Returns `Just` the given value if the conditional is `True`
||| and `Nothing` if the conditional is `False`.
public export
toMaybe : Bool -> Lazy a -> Maybe a
toMaybe True  j = Just j
toMaybe False _ = Nothing

export
Injective Just where
  injective Refl = Refl

||| Convert a `Maybe a` value to an `a` value, using `neutral` in the case
||| that the `Maybe` value is `Nothing`.
public export
lowerMaybe : Monoid a => Maybe a -> a
lowerMaybe Nothing = neutral
lowerMaybe (Just x) = x

||| Returns `Nothing` when applied to `neutral`, and `Just` the value otherwise.
export
raiseToMaybe : Monoid a => Eq a => a -> Maybe a
raiseToMaybe x = if x == neutral then Nothing else Just x

public export
filter : (a -> Bool) -> Maybe a -> Maybe a
filter _ Nothing = Nothing
filter f (Just x) = toMaybe (f x) x

namespace Semigroup

  public export
  [Deep] Semigroup a => Semigroup (Maybe a) where
    Nothing <+> Nothing = Nothing
    Just l  <+> Nothing = Just l
    Nothing <+> Just r  = Just r
    Just l  <+> Just r  = Just $ l <+> r

namespace Monoid

  public export
  [Deep] Semigroup a => Monoid (Maybe a) using Semigroup.Deep where
    neutral = Nothing

public export
Zippable Maybe where
  zipWith f x y = [| f x y |]
  zipWith3 f x y z = [| f x y z |]

  unzipWith f Nothing  = (Nothing, Nothing)
  unzipWith f (Just x) = let (a, b) = f x in (Just a, Just b)

  unzipWith3 f Nothing  = (Nothing, Nothing, Nothing)
  unzipWith3 f (Just x) = let (a, b, c) = f x in (Just a, Just b, Just c)
