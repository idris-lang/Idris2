import Data.Nat

failing "f is not covering."
  f : {n : Nat} -> LT n n -> Void
  f x@LTEZero impossible
