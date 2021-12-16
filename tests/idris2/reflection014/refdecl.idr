import Language.Reflection

%language ElabReflection

fc : FC
fc = EmptyFC

mkEnum : (name : String) -> (cons : List String) -> Elab ()
mkEnum name cons =
  let enumDecl = IData EmptyFC Public Nothing dat
   in declare [enumDecl]
  where enumName : Name
        enumName = UN $ Basic name

        mkCon : String -> ITy
        mkCon n = MkTy EmptyFC EmptyFC (UN $ Basic n) (IVar EmptyFC enumName)

        dat : Data
        dat = MkData EmptyFC enumName (IType EmptyFC) [] (map mkCon cons)

%runElab mkEnum "FooBar" ["Foo","Bar"]

eqFooBar : FooBar -> FooBar -> Bool
eqFooBar Foo Foo = True
eqFooBar Bar Bar = True
eqFooBar _   _   = False

main : IO ()
main =  printLn (eqFooBar Foo Foo)
     >> printLn (eqFooBar Bar Foo)
