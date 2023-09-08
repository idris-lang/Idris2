data MyNat : Type where
     MyZ : MyNat
     MyS : (1 _ : MyNat) -> MyNat

lplus : (1 x : MyNat) -> (1 y : MyNat) -> MyNat
lplus MyZ y = y
lplus (MyS k) y = MyS (lplus k y)

foo : (1 x : MyNat) -> (1 y : MyNat) -> MyNat -> MyNat
foo x y z
    = let 1 test = the MyNat $ case z of
                        MyZ => MyZ
                        (MyS k) => MyS z
            in
          lplus test x
