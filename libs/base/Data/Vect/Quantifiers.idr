module Data.Vect.Quantifiers

import Data.DPair
import Data.Vect

%default total

------------------------------------------------------------------------
-- Types and basic properties

namespace Any
  ||| A proof that some element of a vector satisfies some property
  |||
  ||| @ p the property to be satsified
  public export
  data Any : (0 p : a -> Type) -> Vect n a -> Type where
    ||| A proof that the satisfying element is the first one in the `Vect`
    Here  : {0 xs : Vect n a} -> p x -> Any p (x :: xs)
    ||| A proof that the satsifying element is in the tail of the `Vect`
    There : {0 xs : Vect n a} -> Any p xs -> Any p (x :: xs)

  export
  implementation Uninhabited (Any p Nil) where
    uninhabited (Here _) impossible
    uninhabited (There _) impossible

  export
  implementation {0 p : a -> Type} -> Uninhabited (p x) => Uninhabited (Any p xs) => Uninhabited (Any p $ x::xs) where
    uninhabited (Here y) = uninhabited y
    uninhabited (There y) = uninhabited y

  ||| Eliminator for `Any`
  public export
  anyElim : {0 xs : Vect n a} -> {0 p : a -> Type} -> (Any p xs -> b) -> (p x -> b) -> Any p (x :: xs) -> b
  anyElim _ f (Here p) = f p
  anyElim f _ (There p) = f p

  ||| Given a decision procedure for a property, determine if an element of a
  ||| vector satisfies it.
  |||
  ||| @ p the property to be satisfied
  ||| @ dec the decision procedure
  ||| @ xs the vector to examine
  public export
  any : (dec : (x : a) -> Dec (p x)) -> (xs : Vect n a) -> Dec (Any p xs)
  any _ Nil = No uninhabited
  any p (x::xs) with (p x)
    any p (x::xs) | Yes prf = Yes (Here prf)
    any p (x::xs) | No prf =
      case any p xs of
        Yes prf' => Yes (There prf')
        No prf' => No (anyElim prf' prf)

  export
  mapProperty : (f : forall x. p x -> q x) -> Any p l -> Any q l
  mapProperty f (Here p)  = Here (f p)
  mapProperty f (There p) = There (mapProperty f p)

  export
  toExists : Any p xs -> Exists p
  toExists (Here prf)  = Evidence _ prf
  toExists (There prf) = toExists prf

namespace All
  ||| A proof that all elements of a vector satisfy a property. It is a list of
  ||| proofs, corresponding element-wise to the `Vect`.
  public export
  data All : (0 p : a -> Type) -> Vect n a -> Type where
    Nil  : All p Nil
    (::) : {0 xs : Vect n a} -> p x -> All p xs -> All p (x :: xs)

  ||| If there does not exist an element that satifies the property, then it is
  ||| the case that all elements do not satisfy.
  export
  negAnyAll : {xs : Vect n a} -> Not (Any p xs) -> All (Not . p) xs
  negAnyAll {xs=Nil} _ = Nil
  negAnyAll {xs=(x::xs)} f = (f . Here) :: negAnyAll (f . There)

  export
  notAllHere : {0 p : a -> Type} -> {xs : Vect n a} -> Not (p x) -> Not (All p (x :: xs))
  notAllHere _ Nil impossible
  notAllHere np (p :: _) = np p

  export
  notAllThere : {0 p : a -> Type} -> {xs : Vect n a} -> Not (All p xs) -> Not (All p (x :: xs))
  notAllThere _ Nil impossible
  notAllThere np (_ :: ps) = np ps

  ||| Given a decision procedure for a property, decide whether all elements of
  ||| a vector satisfy it.
  |||
  ||| @ p the property
  ||| @ dec the decision procedure
  ||| @ xs the vector to examine
  public export
  all : (dec : (x : a) -> Dec (p x)) -> (xs : Vect n a) -> Dec (All p xs)
  all _ Nil = Yes Nil
  all d (x::xs) with (d x)
    all d (x::xs) | No prf = No (notAllHere prf)
    all d (x::xs) | Yes prf =
      case all d xs of
        Yes prf' => Yes (prf :: prf')
        No prf' => No (notAllThere prf')

  export
  Either (Uninhabited $ p x) (Uninhabited $ All p xs) => Uninhabited (All p $ x::xs) where
    uninhabited @{Left  _} (px::pxs) = uninhabited px
    uninhabited @{Right _} (px::pxs) = uninhabited pxs

  export
  mapProperty : (f : forall x. p x -> q x) -> All p l -> All q l
  mapProperty f [] = []
  mapProperty f (p::pl) = f p :: mapProperty f pl

  public export
  imapProperty : (0 i : Type -> Type) ->
                 (f : forall a. i a => p a -> q a) ->
                 {0 types : Vect n Type} ->
                 All i types =>
                 All p types -> All q types
  imapProperty _ _              []      = []
  imapProperty i f @{ix :: ixs} (x::xs) = f @{ix} x :: imapProperty i f @{ixs} xs

  public export
  forget : All (const p) {n} xs -> Vect n p
  forget []      = []
  forget (x::xs) = x :: forget xs

  export
  {0 xs : Vect n _} -> All Show (map p xs) => Show (All p xs) where
    show pxs = "[" ++ show' "" pxs ++ "]"
      where
        show' : {0 xs' : Vect n' _} -> String -> All Show (map p xs') => All p xs' -> String
        show' acc @{[]} [] = acc
        show' acc @{[_]} [px] = acc ++ show px
        show' acc @{_ :: _} (px :: pxs) = show' (acc ++ show px ++ ", ") pxs

  ||| A heterogeneous vector of arbitrary types
  public export
  HVect : Vect n Type -> Type
  HVect = All id

  ||| Take the first element.
  export
  head : All p (x :: xs) -> p x
  head (y :: _) = y

  ||| Take all but the first element.
  export
  tail : All p (x :: xs) -> All p xs
  tail (_ :: ys) = ys

  ||| Drop the first n elements given knowledge that
  ||| there are at least n elements available.
  export
  drop : {0 m : _} -> (n : Nat) -> {0 xs : Vect (n + m) a} -> All p xs -> All p (the (Vect m a) (Vect.drop n xs))
  drop 0 ys = ys
  drop (S k) (y :: ys) = drop k ys

  ||| Drop up to the first l elements, stopping early
  ||| if all elements have been dropped.
  export
  drop' : {0 k : _} -> {0 xs : Vect k _} -> (l : Nat) -> All p xs -> All p (Vect.drop' l xs)
  drop' 0 ys = rewrite minusZeroRight k in ys
  drop' (S k) [] = []
  drop' (S k) (y :: ys) = drop' k ys

