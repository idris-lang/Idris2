data Fin : Nat -> Type where
    FZ : Fin (S k)
    FS : Fin k -> Fin (S k)

%builtin Natural Fin

finToInteger : {k : _} -> Fin k -> Integer
finToInteger FZ = 0
finToInteger (FS k) = 1 + finToInteger k

%builtin NaturalToInteger finToInteger
