module Control.Function

public export
interface Injective (f : a -> b) where
  constructor MkInjective
  injective : {x, y : a} -> f x = f y -> x = y

public export
inj : (0 f : a -> b) -> {auto 0 _ : Injective f} -> {0 x, y : a} -> (0 _ : f x = f y) -> x = y
inj _ eq = irrelevantEq (injective eq)
