import Language.Reflection

%language ElabReflection

e1 : TTImp
e1 = `(let x = 5 in x + 2)

p1 : String
p1 = %runElab resugarTerm (Just 20) e1

p2 : String
p2 = %runElab resugarTerm Nothing e1

e2 : TTImp
e2 = `(
  do x <- case y of
            Nice => pure $ nicest
            Just x => x <*> foo "ha"
     let f : Nat -> Nat; f = S . S . S . S . S . S . S . S . S . S
     Z <- f 16
       | S n => 18
     f 2
  )

p3 : String
p3 = %runElab resugarTerm (Just 20) e2

p4 : String
p4 = %runElab resugarTerm Nothing e2

main : IO ()
main = traverse_ (\(n, e) => do putStrLn "\n--------\n\{n}:"; putStrLn e)
  [ ("p1", p1)
  , ("p2", p2)
  , ("p3", p3)
  , ("p4", p4)
  ]
