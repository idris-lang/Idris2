%default total

data Odd : Nat -> Type
data Even : Nat -> Type

data Odd where
  SO : Even n -> Odd (S n)

data Even where
  Z : Even Z
  SE : Odd n -> Even (S n)
