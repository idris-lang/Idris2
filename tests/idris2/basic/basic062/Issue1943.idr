record Foo where
  constructor MkFoo
  (^) : Nat

AFoo : Foo
AFoo = MkFoo { (^) = 42}
