data Fin : Nat -> Type where
  Z : Fin (S n)

irrelevantFin : (k, l : Fin m) -> k === l
irrelevantFin Z Z = Refl

test : (m, n : Nat) -> m === n -> (k : Fin m) -> (l : Fin n) -> k ~=~ l
test m .(m) Refl k l =
  rewrite irrelevantFin k l in
  Refl

test2 : (m, n : Nat) -> m === n -> (k : Fin m) -> (l : Fin n) -> k ~=~ l
test2 .(m) m Refl k l =
  rewrite irrelevantFin l k in
  Refl
