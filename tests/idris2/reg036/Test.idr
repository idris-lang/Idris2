module Test

interface Foo a where
  bar : a -> {auto ok: ()} -> a

foo : Void -> {auto ok: ()} -> Void
foo = ?foo_hole

baz : a -> b -> c -> {auto x : a} -> a
baz {} = x
