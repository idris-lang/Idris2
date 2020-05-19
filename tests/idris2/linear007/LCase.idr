lplus : (1 x : Nat) -> (1 y : Nat) -> Nat
lplus Z y = y
lplus (S k) y = S (lplus k y)

foo : (1 x : Nat) -> (1 y : Nat) -> Nat -> Nat
foo x y z
    = let 1 test = the Nat $ case z of
                        Z => Z
                        (S k) => S z
            in
          lplus test x
