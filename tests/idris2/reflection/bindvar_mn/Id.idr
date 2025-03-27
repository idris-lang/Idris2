module Id

import Language.Reflection

%language ElabReflection

foo : a -> a

definition : Decl
definition =
  let argName = MN "x" 42
   in IDef EmptyFC `{ foo }
        [ PatClause EmptyFC `( foo ~(IBindVar EmptyFC argName) ) (IVar EmptyFC argName)]

%runElab declare (pure definition)

prf : foo 42 = 42
prf = Refl
