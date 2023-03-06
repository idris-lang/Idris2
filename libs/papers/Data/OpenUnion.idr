||| This module is inspired by the open union used in the paper
||| Freer Monads, More Extensible Effects
||| by Oleg Kiselyov and Hiromi Ishii
|||
||| By using an AtIndex proof, we are able to get rid of all of the unsafe
||| coercions in the original module.

module Data.OpenUnion

import Data.DPair
import Data.List.Elem
import Data.List.Quantifiers
import Data.List.AtIndex
import Data.List.HasLength
import Data.Nat
import Data.Nat.Order.Properties
import Decidable.Equality
import Syntax.WithProof
import Control.Monad.Identity
import Control.Monad.Error.Either

%default total

||| An open union of families is an index picking a family out together with
||| a value in the family thus picked.
public export
data UnionF : (elt : a -> Type) -> (ts : List a) -> Type where
  Element : (k : Nat) -> (0 _ : AtIndex t ts k) -> elt t -> UnionF elt ts

||| Open union of types. It's just a type synonym UnionF Identity
public export
Union : List Type -> Type
Union = UnionF Identity

||| An empty open union of families is empty
public export
Uninhabited (UnionF elt []) where
  uninhabited (Element _ p _) = void (uninhabited p)

||| Injecting a value into an open union, provided we know the index of
||| the appropriate type family.
inj' : (k : Nat) -> (0 _ : AtIndex t ts k) -> elt t -> UnionF elt ts
inj' = Element

||| Projecting out of an open union, provided we know the index of the
||| appropriate type family. This may obviously fail if the value stored
||| actually corresponds to another family.
prj' : (k : Nat) -> (0 _ : AtIndex t ts k) -> UnionF elt ts -> Maybe (elt t)
prj' k p (Element k' q t) with (decEq k  k')
  prj' k p (Element k q t) | Yes Refl = rewrite atIndexUnique p q in Just t
  prj' k p (Element k' q t) | No neq = Nothing

||| Given that equality of type families is not decidable, we have to
||| rely on the interface `Member` to automatically find the index of a
||| given family.
public export
inj : Member t ts => elt t -> UnionF elt ts
inj = let (Element n p) = isMember t ts in inj' n p

||| Given that equality of type families is not decidable, we have to
||| rely on the interface `Member` to automatically find the index of a
||| given family.
public export
prj : Member t ts => UnionF elt ts -> Maybe (elt t)
prj = let (Element n p) = isMember t ts in prj' n p

||| By doing a bit of arithmetic we can figure out whether the union's value
||| came from the left or the right list used in the index.
public export
split : Subset Nat (flip HasLength ss) ->
        UnionF elt (ss ++ ts) -> Either (UnionF elt ss) (UnionF elt ts)
split m (Element n p t) with (@@ lt n (fst m))
  split m (Element n p t) | (True ** lt)
    = Left (Element n (strengthenL m lt p) t)
  split m (Element n p t) | (False ** notlt)
    = let 0 lte : lte (fst m) n === True
                = LteIslte (fst m) n (notltIsGTE n (fst m) notlt)
      in Right (Element (minus n (fst m)) (strengthenR m lte p) t)

||| We can inspect an open union over a non-empty list of families to check
||| whether the value it contains belongs either to the first family or any
||| other in the tail.
public export
decompF : UnionF elt (t :: ts) -> Either (UnionF elt ts) (elt t)
decompF (Element 0     (Z)   t) = Right t
decompF (Element (S n) (S p) t) = Left (Element n p t)

public export
decomp : Union (t :: ts) -> Either (Union ts) t
decomp union = map runIdentity $ decompF union

||| An open union over a singleton list is just a wrapper
public export
decomp0F : UnionF elt [t] -> elt t
decomp0F elt = case decompF elt of
  Left t => absurd t
  Right t => t

public export
decomp0 : Union [t] -> t
decomp0 = runIdentity . decomp0F

||| Append new union member
public export
weakenAppend : UnionF elt ts -> UnionF elt (b :: ts)
weakenAppend (Element n p t) = Element (S n) (S p) t

||| Checking if the value belongs to the family at the given index or in the rest of the list
public export
decompAtIndex : {atIndex : AtIndex t xs n} -> UnionF elt xs -> Either (UnionF elt (dropAtIndex xs atIndex)) (elt t)
decompAtIndex {atIndex = Z} (Element 0 Z t) = Right t
decompAtIndex {atIndex = S n} (Element 0 Z t) = Left $ Element 0 Z t
decompAtIndex {atIndex = Z} (Element (S n) (S p) t) = Left $ Element n p t
decompAtIndex {atIndex = S p} (Element (S q) (S n) t) =
  bimap weakenAppend id $ decompAtIndex (Element q n t)

||| Checking if the value belongs to the family being an element t or in the rest of the list
public export
decompElem : {auto elem : Elem t ts} -> UnionF elt ts -> Either (UnionF elt (dropElem ts elem)) (elt t)
decompElem {elem = Here} (Element 0 Z t) = Right t
decompElem {elem = There later} (Element 0 Z t) = Left $ Element 0 Z t
decompElem {elem = Here} (Element (S n) (S p) t) = Left $ Element n p t
decompElem {elem = There later} (Element (S q) (S p) t) =
  bimap weakenAppend id $ decompElem {elem = later} (Element q p t)

public export
weakenUnionElem : {elem : Elem x ts} -> UnionF elt (dropElem ts elem) -> UnionF elt ts
weakenUnionElem {elem = There elem} (Element 0 Z t) = Element 0 Z t
weakenUnionElem {elem = Here} (Element n p t) = (Element (S n) (S p) t)
weakenUnionElem {elem = There elem} (Element (S n) (S p) t) = weakenAppend $ weakenUnionElem {elem} (Element n p t)

decompMember' : {atIndex : Subset Nat (AtIndex t ts)} -> UnionF elt ts -> Either (UnionF elt (dropMember' {t} ts atIndex)) (elt t)
decompMember' {atIndex = Element Z prf1} (Element Z prf2 t) =
  rewrite atIndexUnique prf1 prf2 in Right t
decompMember' {atIndex = Element (S n) prf} (Element 0 Z t) = Left $ Element 0 Z t
decompMember' {atIndex = Element Z prf} (Element (S n) (S p) t) = Left $ Element n p t
decompMember' {atIndex = Element (S n) prf} (Element (S q) (S p) t) =
  bimap weakenAppend id $ decompMember' {atIndex = Element n (inverseS prf)} (Element q p t)


||| Checking if the value belongs to the family being an member t or in the rest of the list
public export
decompMember : {0 ts : List a} -> Member t ts => UnionF elt ts -> Either (UnionF elt (dropMember {t} ts)) (elt t)
decompMember = decompMember' {atIndex = isMember t ts}

||| We can inspect an open union over a list of families, which is an шnterleaving of the other two to check
||| whether the value it contains belongs either to the first family lists (xs) or first family lists (ys).
public export
decompInterleaving : Interleaving xs ys zs -> UnionF elt zs -> Either (UnionF elt xs) (UnionF elt ys)
decompInterleaving Nil (Element n p t) impossible
decompInterleaving (Right interleaving) (Element 0 Z t) = Right (Element 0 Z t)
decompInterleaving (Right interleaving) (Element (S n) (S p) t) =
  bimap id weakenAppend $ decompInterleaving interleaving (Element n p t)
decompInterleaving (Left interleaving) (Element 0 Z t) = Left (Element 0 Z t)
decompInterleaving (Left interleaving) (Element (S n) (S p) t) =
  bimap weakenAppend id $ decompInterleaving interleaving (Element n p t)

||| Inserting new union members on the right leaves the index unchanged.
public export
weakenR : UnionF elt ts -> UnionF elt (ts ++ us)
weakenR (Element n p t) = Element n (weakenR p) t

||| Inserting new union members on the left, requires shifting the index by
||| the number of members introduced. Note that this number is the only
||| thing we need to keep around at runtime.
public export
weakenL : {0 xs : List a}
  -> {default (Element _ (hasLength xs)) hasLen : Subset Nat (flip HasLength xs)}
  -> UnionF elt ys
  -> UnionF elt (xs ++ ys)
weakenL {hasLen} (Element n p t) = Element (fst hasLen + n) (weakenL hasLen p) t

||| Inserting new union members between two lists.
||| Requires length it these lists or themselves.
public export
weaken : {0 xs, ys : List a} ->
 {default (Element _ (hasLength xs)) hasLenXs : Subset Nat (flip HasLength xs)} ->
 {default (Element _ (hasLength ys)) hasLenYs : Subset Nat (flip HasLength ys)} ->
 UnionF elt (xs ++ zs) -> UnionF elt (xs ++ ys ++ zs)
weaken union with (split hasLenXs union)
  weaken union | Left unionXs = weakenR unionXs
  weaken union | Right unionZs =
    let unionYsZs = weakenL {hasLen = hasLenYs} unionZs in
    weakenL {hasLen = hasLenXs} unionYsZs

||| Using a union as an error type in EitherT.
||| This function throws an error if it is a member of the error list.
public export
throwUnionF : (Applicative f, Member x xs) => elt x -> EitherT (UnionF elt xs) f a
throwUnionF = MkEitherT . pure . Left . inj

public export
throwUnion : Applicative f => Member x xs => x -> EitherT (Union xs) f a
throwUnion = throwUnionF . Id

||| Catches an error from the union at Left and returns without it
public export
catchUnionF : {0 xs : List b}
  -> (Monad m, Member t xs)
  => (f t -> EitherT (UnionF f (dropMember {t} xs)) m a)
  -> EitherT (UnionF f xs) m a
  -> EitherT (UnionF f (dropMember {t} xs)) m a
catchUnionF fun = mapEitherT (>>= go)
  where
    go : Either (UnionF f xs) a -> m (Either (UnionF f (dropMember {t} xs)) a)
    go (Right a) = pure (Right a)
    go (Left union) with (decompMember {t} union)
      go (Left union) | Right fx = runEitherT (fun fx)
      go (Left union) | Left rest = pure (Left rest)

public export
catchUnion : {0 xs : List Type}
  -> (Monad m, Member t xs)
  => (t -> EitherT (Union (dropMember {t} xs)) m a)
  -> EitherT (Union xs) m a
  -> EitherT (Union (dropMember {t} xs)) m a
catchUnion fun = catchUnionF (fun . runIdentity)
