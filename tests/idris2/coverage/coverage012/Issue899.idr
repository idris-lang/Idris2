%default total

zeroImpossible : (k : Nat) -> k === Z -> Void
zeroImpossible (S k) eq impossible
