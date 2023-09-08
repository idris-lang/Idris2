import Data.Vect

parameters (len : Nat)
  record Foo where
    constructor Bar
    Gnat : Vect len Nat

foo : Foo 1
foo = Bar _ [0]
