
record Test where
  constructor K
  a : Pair Type Type
  b : fst a -> Void

t : Test
t = K (Nat, Bool) (\ n : Void => n)

