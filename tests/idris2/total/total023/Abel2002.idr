-- adapted from:
-- Andreas Abel, Thorsten Altenkirch
-- A predicative analysis of structural recursion
-- https://doi.org/10.1017/S0956796801004191

data Ord : Type where
  O : Ord
  S : Ord -> Ord
  Lim : (Nat -> Ord) -> Ord

total
addord : Ord -> Ord -> Ord
addord_lim : (Nat -> Ord) -> Ord -> Ord

addord O y = y
addord (S x) y = S (addord x y)
addord (Lim f) y = addord_lim f y

addord_lim f y = Lim (\z => addord (f z) y)
