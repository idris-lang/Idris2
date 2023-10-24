foo : Nat -> Nat
foo a with a
  _ | 0 = a
  _ | S k = a
