module Data.SnocList.Quantifiers

import Data.DPair

import Data.SnocList
import Data.SnocList.Elem

%default total

------------------------------------------------------------------------
-- Types and basic properties

namespace Any

  ||| A proof that some element of a snoclist satisfies some property
  |||
  ||| @ p the property to be satisfied
  public export
  data Any : (0 p : a -> Type) -> SnocList a -> Type where
    ||| A proof that the rightmost element in the `SnocList` satisfies p
    Here  : {0 xs : SnocList a} -> p x -> Any p (xs :< x)
    ||| A proof that there is an element the tail of the `SnocList` satisfying p
    There : {0 xs : SnocList a} -> Any p xs -> Any p (xs :< x)

  export
  Uninhabited (Any p Lin) where
    uninhabited (Here _) impossible
    uninhabited (There _) impossible

  export
  {0 p : a -> Type} ->
    Uninhabited (p x) =>
    Uninhabited (Any p xs) =>
    Uninhabited (Any p (xs :< x)) where
    uninhabited (Here y) = uninhabited y
    uninhabited (There y) = uninhabited y

  ||| Modify the property given a pointwise function
  public export
  mapProperty : (f : {0 x : a} -> p x -> q x) -> Any p l -> Any q l
  mapProperty f (Here p) = Here (f p)
  mapProperty f (There p) = There (mapProperty f p)

  ||| Given a decision procedure for a property, determine if an element of a
  ||| list satisfies it.
  |||
  ||| @ p the property to be satisfied
  ||| @ dec the decision procedure
  ||| @ xs the list to examine
  public export
  any : (dec : (x : a) -> Dec (p x)) -> (xs : SnocList a) -> Dec (Any p xs)
  any _ Lin = No uninhabited
  any p (xs :< x) with (p x)
    any p (xs :< x) | Yes px = Yes (Here px)
    any p (xs :< x) | No npx =
      case any p xs of
        Yes pxs => Yes (There pxs)
        No npxs => No $ \case
          Here px => npx px
          There pxs => npxs pxs

  ||| Forget the membership proof
  export
  toExists : Any p xs -> Exists p
  toExists (Here prf) = Evidence _ prf
  toExists (There prf) = toExists prf

namespace All

  ||| A proof that all elements of a list satisfy a property. It is a list of
  ||| proofs, corresponding element-wise to the `List`.
  public export
  data All : (0 p : a -> Type) -> SnocList a -> Type where
    Lin  : All p [<]
    (:<) : All p xs -> p x -> All p (xs :< x)

  public export
  length : All p xs -> Nat
  length [<] = 0
  length (xs :< x) = S (length xs)

  public export
  (++) : All p xs -> All p ys -> All p (xs ++ ys)
  pxs ++ [<] = pxs
  pxs ++ (pys :< py) = (pxs ++ pys) :< py

  export
  lengthUnfold : (pxs : All p xs) -> length pxs === length xs
  lengthUnfold [<] = Refl
  lengthUnfold (pxs :< _) = cong S (lengthUnfold pxs)


  export
  Either (Uninhabited (p x)) (Uninhabited (All p xs)) => Uninhabited (All p (xs :< x)) where
    uninhabited @{Left  _} (pxs :< px) = uninhabited px
    uninhabited @{Right _} (pxs :< px) = uninhabited pxs

  ||| Modify the property given a pointwise function
  public export
  mapProperty : (f : {0 x : a} -> p x -> q x) -> All p l -> All q l
  mapProperty f [<] = [<]
  mapProperty f (pxs :< px) = mapProperty f pxs :< f px

  ||| Modify the property given a pointwise interface function
  public export
  imapProperty : (0 i : Type -> Type)
              -> (f : {0 a : Type} -> i a => p a -> q a)
              -> {0 types : SnocList Type}
              -> All i types => All p types -> All q types
  imapProperty i f @{[<]} [<] = [<]
  imapProperty i f @{ixs :< ix} (xs :< x) = imapProperty i f @{ixs} xs :< f @{ix} x

  ||| Forget property source for a homogeneous collection of properties
  public export
  forget : All (const type) types -> SnocList type
  forget [<] = [<]
  forget (xs :< x) = forget xs :< x

  ||| Given a decision procedure for a property, decide whether all elements of
  ||| a list satisfy it.
  |||
  ||| @ p the property
  ||| @ dec the decision procedure
  ||| @ xs the list to examine
  public export
  all : (dec : (x : a) -> Dec (p x)) -> (xs : SnocList a) -> Dec (All p xs)
  all _ Lin = Yes Lin
  all d (xs :< x) with (d x)
    all d (xs :< x) | No npx = No $ \(_ :< px) => npx px
    all d (xs :< x) | Yes px =
      case all d xs of
        Yes pxs => Yes (pxs :< px)
        No npxs => No $ \(pxs :< _) => npxs pxs

  export
  zipPropertyWith : (f : {0 x : a} -> p x -> q x -> r x) ->
                    All p xs -> All q xs -> All r xs
  zipPropertyWith f [<] [<] = [<]
  zipPropertyWith f (pxs :< px) (qxs :< qx)
    = zipPropertyWith f pxs qxs :< f px qx

  export
  All Show (map p xs) => Show (All p xs) where
    show pxs = concat ("[<" :: show' pxs ["]"])
      where
        show' : All Show (map p xs') => All p xs' ->
                List String -> List String
        show' @{[<]} [<] = id
        show' @{[<_]} [<px] = (show px ::)
        show' @{_ :< _} (pxs :< px) = show' pxs . (", " ::) . (show px ::)

------------------------------------------------------------------------
-- Relationship between all and any

||| If there does not exist an element that satifies the property, then it is
||| the case that all elements do not satisfy it.
export
negAnyAll : {xs : SnocList a} -> Not (Any p xs) -> All (Not . p) xs
negAnyAll {xs=[<]}     _ = [<]
negAnyAll {xs=xs :< x} f = negAnyAll (f . There) :< (f . Here)

||| If there exists an element that doesn't satify the property, then it is
||| not the case that all elements satisfy it.
export
anyNegAll : Any (Not . p) xs -> Not (All p xs)
anyNegAll (Here npx) (_ :< px) = npx px
anyNegAll (There npxs)  (pxs :< _) = anyNegAll npxs pxs

||| If none of the elements satisfy the property, then not any single one can.
export
allNegAny : All (Not . p) xs -> Not (Any p xs)
allNegAny [<] pxs = absurd pxs
allNegAny (npxs :< npx) (Here px) = absurd (npx px)
allNegAny (npxs :< npx) (There pxs) = allNegAny npxs pxs

||| Given a proof of membership for some element, extract the property proof for it
public export
indexAll : Elem x xs -> All p xs -> p x
indexAll  Here     (_ :< px) = px
indexAll (There e) (pxs :< _) = indexAll e pxs

||| If any `a` either satisfies p or q then given a Snoclist of as,
||| either all values satisfy p
||| or at least one of them sastifies q
public export
decide : ((x : a) -> Either (p x) (q x)) ->
         (xs : SnocList a) -> Either (All p xs) (Any q xs)
decide dec [<] = Left [<]
decide dec (xs :< x) = case dec x of
  Left px => case decide dec xs of
    Left pxs => Left (pxs :< px)
    Right pxs => Right (There pxs)
  Right px => Right (Here px)
