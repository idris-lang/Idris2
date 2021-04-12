
data Fin : Nat -> Type where
    FS : Fin k -> Fin (S k)
    FZ : Fin (S k)

%builtin Natural Fin
