module NonConflict1

export infixr 5 &&&

export
(&&&) : Nat -> Nat -> Nat
(&&&) = minus
