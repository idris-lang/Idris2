import Data.Vect

dvec : (n : Nat) -> {default (replicate n 1) xs : Vect n Nat} -> Nat
dvec n = foldr (+) Z xs
