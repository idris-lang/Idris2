import Language.Reflection

%language ElabReflection
%default total

magicScript : Elab a
magicScript = check $ IAlternative EmptyFC FirstSuccess
  [ `(the Nat 5)
  , `(the String "foo")
  ]

x : Nat
x = %runElab magicScript

y : String
y = %runElab magicScript

-- Check necessary parts of the expected error message

failing "Sorry, I can't find any elaboration which works. All errors:"
  z : Bool
  z = %runElab magicScript

failing "Mismatch between: Nat and Bool"
  z : Bool
  z = %runElab magicScript

failing "Mismatch between: String and Bool"
  z : Bool
  z = %runElab magicScript

-- For the whole error message
z : Bool
z = %runElab magicScript
