bar : (a, b, c, d, e : Unit) -> Unit

foo : (n : Nat) -> Unit
foo 100 = id $ bar () () () () ()
foo _ = ()

bar _ _ _ _ _ = foo 0

