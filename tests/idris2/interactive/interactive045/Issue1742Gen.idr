data Foo : Type where
  MkFoo : (Bar : Bool) -> Foo

Gnu : Foo -> Nat
Gnu x = ?Gnu_rhs_0
