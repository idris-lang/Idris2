module Dummy

import Data.Vect

namespace DList

  ||| A list construct for dependent types.
  |||
  ||| @aTy    The type of the value contained within the list element type.
  ||| @elemTy The type of the elements within the list
  ||| @as     The List used to contain the different values within the type.
  public export
  data DList : (aTy : Type)
            -> (elemTy : aTy -> Type)
            -> (as : List aTy)
            -> Type where
    ||| Create an empty List
    Nil  : DList aTy elemTy Nil
    ||| Cons
    |||
    ||| @elem The element to add
    ||| @rest The list for `elem` to be added to.
    (::) : (elem : elemTy x)
        -> (rest : DList aTy elemTy xs)
        -> DList aTy elemTy (x::xs)

namespace DVect
  ||| A list construct for dependent types.
  |||
  ||| @aTy    The type of the value contained within the list element type.
  ||| @elemTy The type of the elements within the list
  ||| @len    The length of the list.
  ||| @as     The List used to contain the different values within the type.
  public export
  data DVect : (aTy : Type)
            -> (elemTy : aTy -> Type)
            -> (len : Nat)
            -> (as : Vect len aTy)
            -> Type where
    ||| Create an empty List
    Nil  : DVect aTy elemTy Z Nil
    ||| Cons
    |||
    ||| @ex The element to add
    ||| @rest The list for `elem` to be added to.
    (::) : (ex : elemTy x)
        -> (rest : DVect aTy elemTy n xs)
        -> DVect aTy elemTy (S n) (x::xs)

namespace PList
  public export
  data PList : (aTy    : Type)
            -> (elemTy : aTy -> Type)
            -> (predTy : aTy -> Type)
            -> (as     : List aTy)
            -> (prf    : DList aTy predTy as)
            -> Type
    where
      ||| Create an empty List
      Nil  : PList aTy elemTy predTy Nil Nil

      ||| Cons
      |||
      ||| @elem The element to add and proof that the element's type satisfies a certain predicate.
      ||| @rest The list for `elem` to be added to.
      (::) : (elem : elemTy x)
          -> {prf : predTy x}
          -> (rest : PList aTy elemTy predTy xs prfs)
          -> PList aTy elemTy predTy (x :: xs) (prf :: prfs)
