f : {0 a : Type} -> Num a => a
f {a} = g where
  g : Num a => a
  g = fromInteger 0
