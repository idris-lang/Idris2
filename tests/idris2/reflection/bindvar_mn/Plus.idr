module Plus

import Language.Reflection

%language ElabReflection

pls : Nat -> Nat -> Nat

definition : Decl
definition =
  let x = MN "x" 42
      y = DN "y" $ MN "x" 53
  in IDef EmptyFC `{ pls }
          [ PatClause EmptyFC `( pls Z ~(IBindVar EmptyFC y) )
                               (IVar EmptyFC y)
          , PatClause EmptyFC `( pls (S ~(IBindVar EmptyFC x)) ~(IBindVar EmptyFC y) )
                              `( S (pls ~(IVar EmptyFC x) ~(IVar EmptyFC y)) )]

%runElab declare (pure definition)

prf : pls 42 31 = 73
prf = Refl
