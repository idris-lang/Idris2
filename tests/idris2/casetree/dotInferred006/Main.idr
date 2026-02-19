0 foo : (a, b : Type) -> a === b -> Int
foo (_ -> _) _ Refl = 1
foo _ _ _ = 2

0 bar : (a, b : Type) -> a === b -> Int
bar (Int -> _) (_ -> _) Refl = 1
bar _ _ _ = 2

0 baz : (a, b : Type) -> a === b -> Int
baz (Maybe Nat -> _) (Maybe _ -> _) Refl = 1
baz _ _ _ = 2
