module Data.List.Quantifiers

import Data.List
import Data.List.Elem

||| A proof that some element of a list satisfies some property
|||
||| @ p the property to be satsified
public export
data Any : (0 p : a -> Type) -> List a -> Type where
  ||| A proof that the satisfying element is the first one in the `List`
  Here  : {0 xs : List a} -> p x -> Any p (x :: xs)
  ||| A proof that the satsifying element is in the tail of the `List`
  There : {0 xs : List a} -> Any p xs -> Any p (x :: xs)

export
Uninhabited (Any p Nil) where
  uninhabited (Here _) impossible
  uninhabited (There _) impossible

||| Eliminator for `Any`
export
anyElim : (Any p xs -> b) -> (p x -> b) -> Any p (x :: xs) -> b
anyElim _ f (Here p)  = f p
anyElim f _ (There p) = f p

||| Given a decision procedure for a property, determine if an element of a
||| list satisfies it.
|||
||| @ p the property to be satisfied
||| @ dec the decision procedure
||| @ xs the list to examine
export
any : (dec : (x : a) -> Dec (p x)) -> (xs : List a) -> Dec (Any p xs)
any _ Nil = No uninhabited
any p (x::xs) with (p x)
  any p (x::xs) | Yes prf = Yes (Here prf)
  any p (x::xs) | No ctra =
    case any p xs of
      Yes prf' => Yes (There prf')
      No ctra' => No (anyElim ctra' ctra)

||| A proof that all elements of a list satisfy a property. It is a list of
||| proofs, corresponding element-wise to the `List`.
public export
data All : (0 p : a -> Type) -> List a -> Type where
  Nil  : All p Nil
  (::) : {0 xs : List a} -> p x -> All p xs -> All p (x :: xs)

||| If there does not exist an element that satifies the property, then it is
||| the case that all elements do not satisfy it.
export
negAnyAll : {xs : List a} -> Not (Any p xs) -> All (Not . p) xs
negAnyAll {xs=Nil}   _ = Nil
negAnyAll {xs=x::xs} f = (f . Here) :: negAnyAll (f . There)

||| If there exists an element that doesn't satify the property, then it is
||| the case that not all elements satisfy it.
export
negAllAny : Any (Not . p) xs -> Not (All p xs)
negAllAny (Here ctra) (p::_)  = ctra p
negAllAny (There np)  (_::ps) = negAllAny np ps

||| Given a decision procedure for a property, decide whether all elements of
||| a list satisfy it.
|||
||| @ p the property
||| @ dec the decision procedure
||| @ xs the list to examine
export
all : (dec : (x : a) -> Dec (p x)) -> (xs : List a) -> Dec (All p xs)
all _ Nil = Yes Nil
all d (x::xs) with (d x)
  all d (x::xs) | No ctra = No $ \(p::_) => ctra p
  all d (x::xs) | Yes prf =
    case all d xs of
      Yes prf' => Yes (prf :: prf')
      No ctra' => No $ \(_::ps) => ctra' ps

||| Given a proof of membership for some element, extract the property proof for it
export
indexAll : Elem x xs -> All p xs -> p x
indexAll  Here     (p::_  ) = p
indexAll (There e) ( _::ps) = indexAll e ps
