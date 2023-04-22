%default total

foo : List Char -> List Char -> ()
foo (c :: cs) _ = foo (c :: cs) cs
foo _ _ = ()
