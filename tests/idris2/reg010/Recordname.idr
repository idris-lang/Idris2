module Recordname

namespace Foo
  export
  record Name where
    constructor MkName
    foo : Int

  x : Name -> Int
  x = foo

test : Recordname.Foo.Name
