interface A where
  x : Nat
  f : {auto pf : x = 0} -> ()
