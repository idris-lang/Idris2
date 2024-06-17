import Data.Vect

-- m was not in scope when n is implicit
parameters {n : Nat}
    foo : Vect m Nat -> Nat
    foo xs = ?hole

