%default total
namespace Blah
    export
    data Foo : Type where
        MkFoo : Foo

boom : Foo -> Void
boom Z impossible
