module Doc

||| World!
export
world : Nat -> Nat
world x = x*2

nope : Nat
nope = 0

export
||| Hello!
hello : Int -> Int
hello x = x*2

public export
data WrappedInt : Type where
  MkWrappedInt : Int -> WrappedInt

public export
record SimpleRec where
  constructor MkSimpleRec
  a : Int
  b : String

namespace NS

  namespace NestedNS

    ||| A type of Foo
    Foo : Type
    Foo = ()
