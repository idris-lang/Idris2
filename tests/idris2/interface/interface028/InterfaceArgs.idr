interface Decidable p where
  decide : Either p (Not p)

{m, n : Nat} -> Decidable (m === n) where
  decide = go m n where

    go : (m, n : Nat) -> Either (m === n) (Not (m === n))
    go 0 0 = Left Refl
    go 0 (S k) = Right (\case Refl impossible)
    go (S k) 0 = Right (\case Refl impossible)
    go (S k) (S j) = case go k j of
      Left eq => Left (cong S eq)
      Right neq => Right (\case Refl => neq Refl)
