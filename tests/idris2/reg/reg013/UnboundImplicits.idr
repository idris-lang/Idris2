||| Tests for issue #269
import Data.Vect

%unbound_implicits off

record Foo (x : Vect n Nat) where
  constructor MkFoo

parameters (Foo : Vect n Nat)
  bar : Nat
  bar = 0


interface Foo (a : Vect n Nat) where
  baz : Nat

implementation Functor (Vect n) where
