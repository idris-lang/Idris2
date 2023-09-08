%builtin Natural Nat

natToInt : Nat -> Integer
natToInt Z = 0
natToInt (S k) = 1 + natToInt k

%builtin NaturalToInteger natToInt
