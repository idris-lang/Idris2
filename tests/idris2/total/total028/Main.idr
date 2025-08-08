%default total

data X = MkX (Inf X)

foo : X
foo = MkX (assert_total foo)
