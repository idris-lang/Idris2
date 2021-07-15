%default total

isNat : Type -> Bool
isNat Nat = True
isNat (List Char) = False
isNat Int = False
isNat _ = False

trivialEquality : isNat Int = False
trivialEquality = Refl
