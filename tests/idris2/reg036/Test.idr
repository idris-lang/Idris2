module Test

interface Foo a where
  bar : a -> {auto ok: ()} -> a

foo : Void -> {auto ok: ()} -> Void
foo = ?foo_hole
