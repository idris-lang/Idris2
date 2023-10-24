module BadElabScript

import Language.Reflection

%language ElabReflection

x : Elab Nat
x = do
  ignore $ check {expected=Type} `(Nat)
  ?someHole
  check `(%search)

y : Nat
y = %runElab x
