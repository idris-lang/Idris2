||| This module is inspired by the open union used in the paper
||| Freer Monads, More Extensible Effects
||| by Oleg Kiselyov and Hiromi Ishii
|||
||| By using an AtIndex proof, we are able to get rid of all of the unsafe
||| coercions in the original module.

module Data.OpenUnion

import Data.DPair
import Data.List.AtIndex
import Data.List.HasLength
import Data.Nat
import Data.Nat.Order.Properties
import Decidable.Equality
import Syntax.WithProof

%default total

||| An open union of families is an index picking a family out together with
||| a value in the family thus picked.
public export
data Union : (ts : List (a -> Type)) -> a -> Type where
  Element : (k : Nat) -> (0 _ : AtIndex t ts k) -> t v -> Union ts v

||| An empty open union of families is empty
public export
Uninhabited (Union [] v) where uninhabited (Element _ p _) = void (uninhabited p)


||| Injecting a value into an open union, provided we know the index of
||| the appropriate type family.
inj' : (k : Nat) -> (0 _ : AtIndex t ts k) -> t v -> Union ts v
inj' = Element

||| Projecting out of an open union, provided we know the index of the
||| appropriate type family. This may obviously fail if the value stored
||| actually corresponds to another family.
prj' : (k : Nat) -> (0 _ : AtIndex t ts k) -> Union ts v -> Maybe (t v)
prj' k p (Element k' q t) with (decEq k  k')
  prj' k p (Element k q t) | Yes Refl = rewrite atIndexUnique p q in Just t
  prj' k p (Element k' q t) | No neq = Nothing

||| Given that equality of type families is not decidable, we have to rely on
||| the interface `FindElement` to automatically find the index of a given family.
public export
interface FindElement t ts => Member (0 t : a -> Type) (0 ts : List (a -> Type)) where

  inj : t v -> Union ts v
  inj = let (Element n p) = findElement in inj' n p

  prj : Union ts v -> Maybe (t v)
  prj = let (Element n p) = findElement in prj' n p

||| By doing a bit of arithmetic we can figure out whether the union's value came from
||| the left or the right list used in the index.
public export
split : Subset Nat (HasLength ss) -> Union (ss ++ ts) v -> Either (Union ss v) (Union ts v)
split m (Element n p t) with (@@ lt n (fst m))
  split m (Element n p t) | (True ** lt) = Left (Element n (strengthenL m lt p) t)
  split m (Element n p t) | (False ** notlt) =
     let 0 lte : lte (fst m) n === True = LteIslte (fst m) n (notltIsGTE n (fst m) notlt)
     in Right (Element (minus n (fst m)) (strengthenR m lte p) t)

||| We can inspect an open union over a non-empty list of families to check
||| whether the value it contains belongs either to the first family or any
||| other in the tail.
public export
decomp : Union (t :: ts) v -> Either (Union ts v) (t v)
decomp (Element 0     (Z)   t) = Right t
decomp (Element (S n) (S p) t) = Left (Element n p t)

||| An open union over a singleton list is just a wrapper over values of that family
public export
decomp0 : Union [t] v -> t v
decomp0 elt = case decomp elt of
  Left t => absurd t
  Right t => t

||| Inserting new families at the end of the list leaves the index unchanged.
public export
weakenR : Union ts v -> Union (ts ++ us) v
weakenR (Element n p t) = Element n (weakenR p) t

||| If we introduce them at the beginning however, we need to shift the index by
||| the number of families we have introduced. Note that this number is the only
||| thing we need to keep around at runtime.
public export
weakenL : Subset Nat (HasLength ss) -> Union ts v -> Union (ss ++ ts) v
weakenL m (Element n p t) = Element (fst m + n) (weakenL m p) t
