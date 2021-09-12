
f : (Nat -> Nat) -> Nat
f k = f \n => k (S n)

g : Nat -> Nat
g x = f ?a
