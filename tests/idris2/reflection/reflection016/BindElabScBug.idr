import Language.Reflection

%default total

f : TTImp -> Elab Nat
f _ = pure 5

%language ElabReflection

x = %runElab quote 4 >>= f
