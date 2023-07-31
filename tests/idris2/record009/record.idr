parameters (X : Nat)
  Foo : Type
  Foo = Nat

  record Bar (xs : List a) where
    constructor MkBar
    Gnu : Foo

  Baz : Foo -> Nat
  Baz x = x

  Quux : Bar xs -> Foo
  Quux x = Gnu x
