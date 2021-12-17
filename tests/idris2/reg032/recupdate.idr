record R (a : Type) where
  constructor MkR
  x : a

rmap : (a -> b) -> R a -> R b
rmap f = { x $= f }
