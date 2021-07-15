fstDup: (xs : List a) -> map fst (map dup xs) === xs
fstDup Nil = Refl
fstDup (x::xs) = ?a
