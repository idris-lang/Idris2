doPlus : Nat -> Nat -> Nat
doPlus x y = x `plus` y

doMult : Nat -> Nat -> Nat
doMult x y = x `mult` y

doMinus : Nat -> Nat -> Nat
doMinus x y = x `minus` y

doEqual : (m, n : Nat) -> Bool
doEqual m n = m `equalNat` n

doCompare : (m, n : Nat) -> Ordering
doCompare m n = m `compareNat` n
