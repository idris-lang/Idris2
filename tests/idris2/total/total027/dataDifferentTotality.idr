total
data X : Type

partial
data X where
  MkX : (X -> X) -> X
