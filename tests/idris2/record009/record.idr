parameters (X : Nat)
  Foo : Type
  Foo = Nat

  record Bar where
    constructor MkBar
    Gnu : Foo

  Baz : Foo -> Nat
  Baz x = x

  Quux : Bar -> Foo
  Quux x = Gnu x
