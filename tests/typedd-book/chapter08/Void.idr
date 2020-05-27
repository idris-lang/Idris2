twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

valueNotSuc : (x : Nat) -> x = S x -> Void
valueNotSuc _ Refl impossible

loop : Void
loop = loop

partial
nohead : Void
nohead = getHead []
  where
    partial
    getHead : List Void -> Void
    getHead (x :: xs) = x
