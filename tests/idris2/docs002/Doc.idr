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

namespace NS

  namespace NestedNS

    ||| A type of Foo
    Foo : Type
    Foo = ()
