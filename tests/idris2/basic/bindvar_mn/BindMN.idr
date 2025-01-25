import Language.Reflection

%language ElabReflection

foo : a -> a

definition : Decl
definition =
  let fooName = UN $ Basic "foo"
      argName = MN "x" 42
   in IDef EmptyFC fooName
        [ PatClause EmptyFC
                    (IApp EmptyFC (IVar EmptyFC fooName)
                                  (IBindVar EmptyFC argName))
                    (IVar EmptyFC argName)]

%runElab declare (pure definition)

prf : foo 42 = 42
prf = Refl
