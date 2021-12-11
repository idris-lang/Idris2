
%prefix_record_projections off

data T : Nat -> Type where
  MkT : (n : Nat) -> T n

record R where
  n : Nat
  x : T n
