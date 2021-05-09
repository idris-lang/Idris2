module Data.List.Quantifiers

import Data.DPair

import Data.List
import Data.List.Elem

%default total

------------------------------------------------------------------------
-- Types and basic properties

namespace Any

  ||| A proof that some element of a list satisfies some property
  |||
  ||| @ p the property to be satisfied
  public export
  data Any : (0 p : a -> Type) -> List a -> Type where
    ||| A proof that the satisfying element is the first one in the `List`
    Here  : {0 xs : List a} -> p x -> Any p (x :: xs)
    ||| A proof that the satisfying element is in the tail of the `List`
    There : {0 xs : List a} -> Any p xs -> Any p (x :: xs)

  export
  Uninhabited (Any p Nil) where
    uninhabited (Here _) impossible
    uninhabited (There _) impossible


  ||| Modify the property given a pointwise function
  export
  mapProperty : (f : {0 x : a} -> p x -> q x) -> Any p l -> Any q l
  mapProperty f (Here p) = Here (f p)
  mapProperty f (There p) = There (mapProperty f p)

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
        No ctra' => No $ \case
          Here px => ctra px
          There pxs => ctra' pxs

  ||| Forget the membership proof
  export
  toExists : Any p xs -> Exists p
  toExists (Here prf) = Evidence _ prf
  toExists (There prf) = toExists prf

namespace All

  ||| A proof that all elements of a list satisfy a property. It is a list of
  ||| proofs, corresponding element-wise to the `List`.
  public export
  data All : (0 p : a -> Type) -> List a -> Type where
    Nil  : All p Nil
    (::) : {0 xs : List a} -> p x -> All p xs -> All p (x :: xs)


  ||| Modify the property given a pointwise function
  export
  mapProperty : (f : {0 x : a} -> p x -> q x) -> All p l -> All q l
  mapProperty f [] = []
  mapProperty f (p::pl) = f p :: mapProperty f pl

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

  export
  zipPropertyWith : (f : {0 x : a} -> p x -> q x -> r x) ->
                    All p xs -> All q xs -> All r xs
  zipPropertyWith f [] [] = []
  zipPropertyWith f (px :: pxs) (qx :: qxs)
    = f px qx :: zipPropertyWith f pxs qxs

------------------------------------------------------------------------
-- Relationship between all and any

||| If there does not exist an element that satifies the property, then it is
||| the case that all elements do not satisfy it.
export
negAnyAll : {xs : List a} -> Not (Any p xs) -> All (Not . p) xs
negAnyAll {xs=Nil}   _ = Nil
negAnyAll {xs=x::xs} f = (f . Here) :: negAnyAll (f . There)

||| If there exists an element that doesn't satify the property, then it is
||| not the case that all elements satisfy it.
export
anyNegAll : Any (Not . p) xs -> Not (All p xs)
anyNegAll (Here ctra) (p::_)  = ctra p
anyNegAll (There np)  (_::ps) = anyNegAll np ps

||| If none of the elements satisfy the property, then not any single one can.
export
allNegAny : All (Not . p) xs -> Not (Any p xs)
allNegAny [] p = absurd p
allNegAny (np :: npxs) (Here p) = absurd (np p)
allNegAny (np :: npxs) (There p) = allNegAny npxs p

||| Given a proof of membership for some element, extract the property proof for it
public export
indexAll : Elem x xs -> All p xs -> p x
indexAll  Here     (p::_  ) = p
indexAll (There e) ( _::ps) = indexAll e ps

--- Relations between listwise `All` and elementwise `Subset` ---

||| Push in the property from the list level with element level
public export
pushIn : (xs : List a) -> (0 _ : All p xs) -> List $ Subset a p
pushIn []      []      = []
pushIn (x::xs) (p::ps) = Element x p :: pushIn xs ps

||| Pull the elementwise property out to the list level
public export
pullOut : (xs : List $ Subset a p) -> Subset (List a) (All p)
pullOut [] = Element [] []
pullOut (Element x p :: xs) = let Element ss ps = pullOut xs in Element (x::ss) (p::ps)

export
pushInOutInverse : (xs : List a) -> (0 prf : All p xs) -> pullOut (pushIn xs prf) = Element xs prf
pushInOutInverse [] [] = Refl
pushInOutInverse (x::xs) (p::ps) = rewrite pushInOutInverse xs ps in Refl

export
pushOutInInverse : (xs : List $ Subset a p) -> uncurry Quantifiers.pushIn (pullOut xs) = xs
pushOutInInverse [] = Refl
pushOutInInverse (Element x p :: xs) with (pushOutInInverse xs)
  pushOutInInverse (Element x p :: xs) | subprf with (pullOut xs)
    pushOutInInverse (Element x p :: xs) | subprf | Element ss ps = rewrite subprf in Refl
