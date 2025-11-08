fnc : (a : Nat) -> (b : Nat) -> (a > b) = True -> Type
fnc 0 0 Refl impossible
fnc 0 (S _) Refl impossible
fnc (S k) b prf = ?fnc_rhs_1
