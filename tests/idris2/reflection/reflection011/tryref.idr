import Language.Reflection

%language ElabReflection

elabTry : Elab ()
elabTry
    = try (declare `[ x : 94
                      x = 94 ])
          (declare `[ x : Int
                      x = 94 ])

%runElab elabTry
