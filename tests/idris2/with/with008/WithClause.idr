data IsS : Nat -> Type where
  S : (n : Nat) -> IsS (S n)

isS : (n : Nat) -> Maybe (IsS n)
isS (S n) = Just (S n)
isS _ = Nothing

pred : Nat -> Nat
pred n with (isS n)
  _ | Nothing = Z
  _ | Just (S n) = n
