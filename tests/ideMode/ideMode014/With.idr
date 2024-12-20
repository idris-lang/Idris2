module With

f : (n : Nat) -> (m : Nat ** n : Nat ** m = n + n)
f n with (n + n) proof eq
  f n | Z     = (Z ** n ** sym eq)
  f n | (S m) = (S m ** n ** sym eq)

g : List a -> Nat
g [] = Z
g (a :: as) with (as ++ as)
  g (b :: bs) | asas = Z

nested : Nat -> Nat
nested m with (m)
  nested m | Z with (m + m)
    nested m | Z | 0 = 1
    nested m | Z | S k with (k + k)
      nested m | Z | S k | Z = 2
      nested m | Z | S k | S l with (l + l)
        nested m | Z | S k | S l | Z = 3
        nested m | Z | S k | S l | S p = 4
  nested m | S k = 5

data ANat : Nat -> Type where
  MkANat : (n : Nat) -> ANat n

someNats : Nat -> Nat
someNats n with (MkANat n)
  someNats n | m@(MkANat n) with (MkANat n)
    someNats n | p@(MkANat n) | MkANat n = Z
