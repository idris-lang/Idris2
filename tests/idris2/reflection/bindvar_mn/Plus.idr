module Plus

import Language.Reflection

%language ElabReflection

pls : Nat -> Nat -> Nat

definition : Decl
definition =
  let z = UN $ Basic "Z"
      s = UN $ Basic "S"
      plusName = UN $ Basic "pls"
      x = MN "x" 42
      y = DN "y" $ MN "x" 53
  in IDef EmptyFC plusName
          [ PatClause EmptyFC (IApp EmptyFC (IApp EmptyFC (IVar EmptyFC plusName) (IVar EmptyFC z))
                                            (IBindVar EmptyFC y))
                              (IVar EmptyFC y)
          , PatClause EmptyFC (IApp EmptyFC (IApp EmptyFC (IVar EmptyFC plusName) (IApp EmptyFC (IVar EmptyFC s) (IBindVar EmptyFC x)))
                                            (IBindVar EmptyFC y))
                              (IApp EmptyFC (IVar EmptyFC s)
                                            (IApp EmptyFC (IApp EmptyFC (IVar EmptyFC plusName) (IVar EmptyFC x))
                                                          (IVar EmptyFC y)))]

%runElab declare (pure definition)

prf : pls 42 31 = 73
prf = Refl
