data MyUnit : Type

interface I a where
  foo : a

I MyUnit
-- I Main.MyUnit
-- TODO: https://github.com/idris-lang/Idris2/issues/3601

namespace X
  export
  T : Type
  T = MyUnit

  export
  I T

  failing "Multiple solutions found in search"
    x' = foo {a=MyUnit}

x = foo {a=MyUnit}
