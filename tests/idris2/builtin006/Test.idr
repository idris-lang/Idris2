data MyNat
    = Z
    | S MyNat

natToInt : MyNat -> Integer
natToInt Z = 0
natToInt (S k) = 1 + natToInt k

%builtin NaturalToInteger natToInt
