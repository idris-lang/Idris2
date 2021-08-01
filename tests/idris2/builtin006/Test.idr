data MyNat
    = Z
    | S MyNat MyNat

natToInt : MyNat -> Integer
natToInt Z = 0
natToInt (S k _) = 1 + natToInt k

%builtin NaturalToInteger natToInt
