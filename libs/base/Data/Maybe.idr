module Data.Maybe

public export
isNothing : Maybe a -> Bool
isNothing Nothing  = True
isNothing (Just j) = False

public export
isJust : Maybe a -> Bool
isJust Nothing  = False
isJust (Just j) = True

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
isItJust (Just x) = Yes ItIsJust
isItJust Nothing = No absurd

||| Convert a `Maybe a` value to an `a` value by providing a default `a` value
||| in the case that the `Maybe` value is `Nothing`.
public export
fromMaybe : (Lazy a) -> Maybe a -> a
fromMaybe def Nothing  = def
fromMaybe def (Just j) = j

||| Returns the `a` value of a `Maybe a` which is proved `Just`.
public export
fromJust : (v : Maybe a) -> IsJust v => a
fromJust (Just x) = x
fromJust Nothing impossible

||| Returns `Just` the given value if the conditional is `True`
||| and `Nothing` if the conditional is `False`.
public export
toMaybe : Bool -> Lazy a -> Maybe a
toMaybe True  j = Just j
toMaybe False j = Nothing

export
justInjective : {x : t} -> {y : t} -> (Just x = Just y) -> x = y
justInjective Refl = Refl

||| Convert a `Maybe a` value to an `a` value, using `neutral` in the case
||| that the `Maybe` value is `Nothing`.
public export
lowerMaybe : Monoid a => Maybe a -> a
lowerMaybe Nothing = neutral
lowerMaybe (Just x) = x

||| Returns `Nothing` when applied to `neutral`, and `Just` the value otherwise.
export
raiseToMaybe : (Monoid a, Eq a) => a -> Maybe a
raiseToMaybe x = if x == neutral then Nothing else Just x

