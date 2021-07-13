data Foo : Type where
  |||An A
  A ,
  ||| Just a B
  B : Foo


public export
foo1, foo2 : Foo
foo1 = A
foo2 = LocalB
  where
    LocalB, LocalA : Foo
    LocalB = B
    LocalA = let NestedLocalA, NestedLocalB : Foo
                 NestedLocalA = A
                 NestedLocalB = B
             in NestedLocalA
