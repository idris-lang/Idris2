interface Cogen a where
  constructor MkCogen
  perturb : a -> Nat -> Nat

Cogen Void where
  perturb _ impossible
