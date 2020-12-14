interface Add a where
  add : a -> a

testAdd : Nat -> Nat -> Nat
testAdd x y = add x
  where
    Add Nat where
      add Z = y
      add (S k) = add k
