
fun1 : a -> a
fun1 x = x

{-

allow unclosed comment block at the end of file

{-
fun2 : a -> a
fun2 x = x
-}

-- Before implemneting #2098, this was somehow parsed as a valid source and `fun3` was in scope
--
-- But i don't think that's the supposed behaviour for nested comment blocks?
-- In any case, after the change, `fun3` now is commented out.

fun3 : a -> a
fun3 x = x
