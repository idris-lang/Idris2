import Language.Reflection

x : TTImp
x = `(with Prelude.Nil [])

%language ElabReflection

x' : Elab (List Nat)
x' = check x

l : List Nat
l = 1 :: %runElab x'
