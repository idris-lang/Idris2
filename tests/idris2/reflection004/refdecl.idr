import Language.Reflection

%language ElabReflection

logDecls : TTImp -> Elab (Int -> Int)
logDecls v
    = do declare [IClaim EmptyFC MW Public []
                 (MkTy EmptyFC `{{ Main.foo }}
                               `(Int -> Int -> Int) )]

         declare `[ foo x y = x + y ]

         declare `[ multBy : Int -> Int
                    multBy x = x * ~(v) ]
         declare `[ myplus : Nat -> Nat -> Nat
                    myplus Z y = y
                    myplus (S k) y = S (myplus k y) ]
         check `( multBy )

mkMult : Int -> Int
mkMult = %runElab logDecls `(4)
