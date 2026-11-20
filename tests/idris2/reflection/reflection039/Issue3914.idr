import Language.Reflection

%language ElabReflection

baz : (0 _ : Unit) -> Integer
baz = %runElab check $ ILam emptyFC MW ExplicitArg Nothing `(Unit) `(42)
