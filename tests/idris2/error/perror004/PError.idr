foo : Nat -> Nat -> Bool
foo x y with (x == y)
  foo x y | True with (y == x)
    foo x y | True | False | 10 = x
    foo x y | True | True = x
  foo x y | False = y
