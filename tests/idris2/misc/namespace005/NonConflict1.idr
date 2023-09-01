module NonConflict1

infixr 5 &&&

export
(&&&) : Nat -> Nat -> Nat
(&&&) = minus

