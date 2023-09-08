record Foo where
  constructor MkFoo
  a : Nat
  b : Nat

foo1 : Foo
foo1 = MkFoo
  { a = 1
  , a = 2
  , b = 3
  }

foo2 : Foo
foo2 =
  { a := 3
  , a := 4
  , b := 2
  , b := 1
  } foo1
