import Data.Vect

foo : {n : Nat} -> Vect n Nat -> Nat
foo {n=Z} _ = 42
