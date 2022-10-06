%default total

test : (0 n : Nat) -> Type -> Type
test n a with 0 (n + n)
  _ | twon = a
