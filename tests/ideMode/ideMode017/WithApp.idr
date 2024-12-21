data Natty : Nat -> Type where
  Z : Natty Z
  S : Natty n -> Natty (S n)

view : (n: Nat) -> Natty n
view Z = Z
view (S n) = S (view n)

id : Nat -> Nat
id n with (view n)
  id _ | Z = Z
  id _ | S n = id _ | n
