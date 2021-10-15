module Control.Function

public export
interface Injective (f : a -> b) where
  constructor MkInjective
  injective : {x, y : a} -> f x = f y -> x = y

public export
inj : (f : a -> b) -> Injective f => {x, y : a} -> f x = f y -> x = y
inj _ = injective
