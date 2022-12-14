-- %logging 5

interface Interface specifier where
  0 concrete : specifier -> Type

record Value s where
  constructor MkValue
  specifier : s

0 DependentValue : Interface s => Value s -> Type
DependentValue v = concrete (specifier v)

data Record : s -> Type where
  MkRecord : Value s -> DependentValue {s} value -> Record s
