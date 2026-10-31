
foo : ({a : Nat} -> {b : Unit} -> Nat) -> Nat
foo f = f {a=42} {b = ()}

callFoo : Nat
callFoo = foo $ \ {x}, {y} => x

failing "Mismatch between: () and Nat"
  callFoo2 : Nat
  callFoo2 = foo $ \ {x}, {x} => x

failing "Mismatch between: () and Nat"
  callFoo2 : Nat
  callFoo2 = foo $ \ {x}, {y} => y

main : IO ()
main = printLn $ callFoo

