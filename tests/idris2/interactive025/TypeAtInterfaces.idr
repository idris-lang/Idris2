||| Test if :typeat can report the type of variables in interface definitions
||| and implementations

interface Nattable a where
  toNat : a -> Nat

Nattable Bool where
  -- Create some variables just to test
  toNat True  = let x = 0 in S x
  toNat False = let y = 0 in y
