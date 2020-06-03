import Language.Reflection

%language ElabReflection

mkDecls : TTImp -> Elab ()
mkDecls v
    = declare `[ mkMult : Int -> Int
                 mkMult x = x * ~(v) ]

%runElab mkDecls `(94)

bad : a
bad = %runElab mkDecls `(94)
