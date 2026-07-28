data X : Nat -> Type where
  XS : X (S n)

f : () -> (n : Nat) -> X n -> Nat
f b@() .(S m) XS = ?hole
