totalLen : List String -> Nat
totalLen xs = foldr (\str, len => length str + len) 0 xs
