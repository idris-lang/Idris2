module With

f : (n : Nat) -> (m : Nat ** n : Nat ** m = n + n)
f n with (n + n) proof eq
  f n | Z     = (Z ** n ** sym eq)
  f n | (S m) = (S m ** n ** sym eq)
