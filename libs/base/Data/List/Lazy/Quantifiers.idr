||| WIP: same as Data.List.Quantifiers but for lazy lists

module Data.List.Lazy.Quantifiers

import Data.DPair
import Data.List.Lazy

%default total

namespace Any

  -- Note: it is crucial here that we mark `xs` as `Lazy`, otherwise Idris
  --  will happily use `Delay` in the return index and give us a badly-behaved
  -- family!
  public export
  data Any : (p : a -> Type) -> (xs : LazyList a) -> Type where
    Here  : {0 xs : Lazy (LazyList a)} -> p x -> Any p (x :: xs)
    There : {0 xs : Lazy (LazyList a)} -> Any p xs -> Any p (x :: xs)

  public export
  toExists : Any p xs -> Exists p
  toExists (Here prf) = Evidence _ prf
  toExists (There p) = toExists p

  public export
  toDPair : {xs : LazyList a} -> Any p xs -> DPair a p
  toDPair (Here prf) = (_ ** prf)
  toDPair (There p) = toDPair p

  export
  Uninhabited (Any p Nil) where
    uninhabited (Here _) impossible
    uninhabited (There _) impossible

  export
  {0 p : a -> Type} -> Uninhabited (p x) => Uninhabited (Any p xs) => Uninhabited (Any p $ x::xs) where
    uninhabited (Here y) = uninhabited y
    uninhabited (There y) = uninhabited y

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
  public export
  any : (dec : (x : a) -> Dec (p x)) -> (xs : LazyList a) -> Dec (Any p xs)
  any _ Nil = No uninhabited
  any p (x::xs) with (p x)
    any p (x::xs) | Yes prf = Yes (Here prf)
    any p (x::xs) | No ctra =
      case any p xs of
        Yes prf' => Yes (There prf')
        No ctra' => No $ \case
          Here px => ctra px
          There pxs => ctra' pxs

  public export
  pushOut : Functor p => Any (p . q) xs -> p $ Any q xs
  pushOut @{fp} (Here v)  = map @{fp} Here v
  pushOut @{fp} (There n) = map @{fp} There $ pushOut n
