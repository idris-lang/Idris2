import Data.Vect

parameters (x : Nat, y : Nat)
  addAll : Nat -> Nat
  addAll z = x + y + z

parameters (y : Nat, xs : Vect x a)
  data Vects : Type -> Type where
    MkVects : Vect y a -> Vects a

  append : Vects a -> Vect (x + y) a
  append (MkVects ys) = xs ++ ys
