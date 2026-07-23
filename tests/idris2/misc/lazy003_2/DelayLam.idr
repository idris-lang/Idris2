-- See https://github.com/idris-lang/Idris2/issues/1066

foo : Inf (Unit -> Unit)
foo = \x => x

bar : Inf (Unit -> Unit)
bar = Delay (\x => x)
