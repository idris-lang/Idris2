module FailingTotality

%default total

failing "x is not covering."

  x : Bool -> Nat
  x True = 0


failing """
x is not total, possibly not terminating due to recursive
path FailingTotality.x
"""

  x : Bool
  x = x

failing "D is not total, not strictly positive"

  data D : Type where
    Lam : (D -> D) -> D

