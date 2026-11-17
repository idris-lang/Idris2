import Language.Reflection

%language ElabReflection

foo : (1 _ : Unit) -> Unit
foo = %runElab check `(\x => x)
