import Decidable.Equality

0 foo : (i, j : Nat) -> Bool
foo i j = case decEq i j of
            Yes pf => True
            No  pf => False
