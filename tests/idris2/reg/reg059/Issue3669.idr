data X : Nat -> Type where
  XS : X (S n)

f : (n : Nat) -> X n -> ()
f s@(.(S n)) XS with (s)
  _ | _ = ()
