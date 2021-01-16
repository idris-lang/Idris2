
eq1 : (x : Nat) -> (x = S x) -> Nat
eq1 x p impossible

eq2 : (x : Nat) -> (S x = Z) -> Nat
eq2 x p impossible

eq3 : (x : Nat) -> (S (S x) = (S x)) -> Nat
eq3 x p impossible

eq4 : (x : Nat) -> (S x = x) -> Nat
eq4 x p impossible

eq5 : (x : Nat) -> (Z = S x) -> Nat
eq5 x p impossible

eq6 : (x : Nat) -> (S x = (S (S x))) -> Nat
eq6 x p impossible

eqL1 : (xs : List a) -> (x :: xs = []) -> Nat
eqL1 xs p impossible

eqL2 : (xs : List a) -> (x :: xs = x :: y :: xs) -> Nat
eqL2 xs p impossible

badeq : (x : Nat) -> (y : Nat) -> (S (S x) = S y) -> Nat
badeq x y p impossible

badeqL : (xs : List a) -> (ys : List a) -> (x :: xs = x :: y :: ys) -> Nat
badeqL xs ys p impossible
