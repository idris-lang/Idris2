module Uninh

data MyElem : a -> List a -> Type where
  MyHere : MyElem x (x :: xs)
  MyThere : (later : MyElem x xs) -> MyElem x (y :: xs)

noIndent : (MyElem a []) -> Void
noIndent c = ?noIndent_rhs

Uninhabited (MyElem a []) where
  uninhabited c = ?uninhabited_rhs

