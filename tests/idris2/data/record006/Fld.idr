record Is3 (n : Nat) where
  constructor MkThree
  {auto prf : n === 3}

three : Is3 3
three = MkThree
