namespace X
  export
  OneX : Bool -> Bool

namespace Y
  export
  data Foo = OneX

foo : Bool
foo = OneX (id False)
