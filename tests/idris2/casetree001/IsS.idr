data IsS : (Nat -> Nat) -> Type where
  Indeed : {s : Nat -> Nat} -> s === S -> IsS s

indeed : IsS S -> Nat
indeed (Indeed _) = Z
