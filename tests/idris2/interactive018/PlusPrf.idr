%hint
mycong : (f : a -> b) -> x = y -> f x = f y
mycong f Refl = Refl

plusZ : (n : Nat) -> plus n Z = n

plusS : (n : Nat) -> (m : Nat) -> plus n (S m) = S (plus n m)
