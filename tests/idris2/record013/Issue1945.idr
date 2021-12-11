-- this works
aNat : {default Z theNat : Nat} -> Nat
aNat = theNat

-- this does too, now (but did not work before)
record ANat where
  constructor MkANat
  {default Z theNat : Nat}

-- let's try out
ex : ANat
ex = MkANat
