idMatch : Type -> Bool
idMatch ((x : Type) -> x) = True
idMatch _ = False
