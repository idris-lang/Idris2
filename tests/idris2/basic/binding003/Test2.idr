import Data.Fin


typebind
record Sigma (ty : Type) (sy : ty -> Type) where
  constructor S
  p1 : ty
  p2 : sy p1


List : Type -> Type
List a = Sigma (n <- Nat) | Fin n -> a
