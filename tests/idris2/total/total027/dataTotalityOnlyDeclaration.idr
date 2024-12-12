total
data X : Type

data X where
  MkX : (X -> X) -> X
