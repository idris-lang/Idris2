total
notHack : Nat -> (Nat, Nat)
notHack Z = (Z, Z)
notHack (S n) = let (baz1, baz2) = notHack n
                in (baz2, S baz1)


total
hack : Nat -> (Void, Void)
hack n = let (baz1, baz2) = hack n
         in (baz1, baz2)
