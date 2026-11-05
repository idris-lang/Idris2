import Deriving.Show

%language ElabReflection

record X k where
  constructor MkX
  unX : List k

Show k => Show (X k) where
  show m = ""

record Y where
  constructor MkY
  x : X Nat

showY : Show Y
showY = %runElab derive
