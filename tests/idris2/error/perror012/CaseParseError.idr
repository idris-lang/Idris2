plus : Nat -> Nat -> Nat
plus m n = case m of
  Z => n
  S m -> S (plus m n)
