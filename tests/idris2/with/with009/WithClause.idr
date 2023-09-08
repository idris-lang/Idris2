data IsS : Nat -> Type where
  S : (n : Nat) -> IsS (S n)

isS : (n : Nat) -> Maybe (IsS n)
isS (S n) = Just (S n)
isS _ = Nothing

failing "Pattern variable n unifies with: S ?m"

  pred : Nat -> Nat
  pred n with (isS n)
    _ | Nothing = Z
    _ | Just (S m) = m

pred : {n : Nat} -> Nat
pred with (isS n)
  _ | Nothing = Z
  _ | Just (S m) = m
