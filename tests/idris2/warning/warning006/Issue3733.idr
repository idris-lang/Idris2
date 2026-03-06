data X = MkX Int String

foo : X -> Int
foo (MkX x) impossible
foo (MkX x s) = x
foo (MkX n s x) impossible
