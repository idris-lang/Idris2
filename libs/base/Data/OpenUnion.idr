||| This module is inspired by the open union used in the paper
||| Freer Monads, More Extensible Effects
||| by Oleg Kiselyov and Hiromi Ishii
|||
||| By using an AtIndex proof, we are able to get rid of all of
||| the unsafe coercions in the original module.

module Data.OpenUnion

import Data.DPair
import Data.List.AtIndex
import Data.List.HasLength
import Data.Nat
import Data.Nat.Order.Properties
import Decidable.Equality
import Syntax.WithProof

%default total

||| An open union transformer takes
||| @ts   a list of type descriptions
||| @elt  a method to turn descriptions into types
||| and returns a union of the types described in the list.
||| Elements are given by an index selecting a value in the list
||| together with a value of the appropriately decoded type.
public export
data UnionT : (elt : a -> Type) -> (ts : List a) -> Type where
  Element : (k : Nat) -> (0 _ : AtIndex t ts k) -> elt t -> UnionT elt ts

||| A union of types is obtained by taking the union transformer
||| where the decoding function is the identity.
public export
Union : List Type -> Type
Union = UnionT Prelude.id

||| An empty open union of families is empty
public export
Uninhabited (UnionT elt []) where
  uninhabited (Element _ p _) = void (uninhabited p)

||| Injecting a value into an open union, provided we know the index of
||| the appropriate type family.
export
inj : (k : Nat) -> (0 _ : AtIndex t ts k) -> elt t -> UnionT elt ts
inj = Element

||| Projecting out of an open union, provided we know the index of the
||| appropriate type family. This may obviously fail if the value stored
||| actually corresponds to another family.
export
prj : (k : Nat) -> (0 _ : AtIndex t ts k) -> UnionT elt ts -> Maybe (elt t)
prj k p (Element k' q t) with (decEq k  k')
  prj k p (Element k q t) | Yes Refl = rewrite atIndexUnique p q in Just t
  prj k p (Element k' q t) | No neq = Nothing

||| By doing a bit of arithmetic we can figure out whether the union's value
||| came from the left or the right list used in the index.
public export
split : Subset Nat (flip HasLength ss) ->
        UnionT elt (ss ++ ts) -> Either (UnionT elt ss) (UnionT elt ts)
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
decomp : UnionT elt (t :: ts) -> Either (UnionT elt ts) (elt t)
decomp (Element 0     (Z)   t) = Right t
decomp (Element (S n) (S p) t) = Left (Element n p t)

||| An open union over a singleton list is just a wrapper
public export
decomp0 : UnionT elt [t] -> elt t
decomp0 elt = case decomp elt of
  Left t => absurd t
  Right t => t

||| Inserting new union members on the right leaves the index unchanged.
public export
weakenR : UnionT elt ts -> UnionT elt (ts ++ us)
weakenR (Element n p t) = Element n (weakenR p) t

||| Inserting new union members on the left, requires shifting the index by
||| the number of members introduced. Note that this number is the only
||| thing we need to keep around at runtime.
public export
weakenL : Subset Nat (flip HasLength ss) -> UnionT elt ts -> UnionT elt (ss ++ ts)
weakenL m (Element n p t) = Element (fst m + n) (weakenL m p) t
