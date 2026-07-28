plusRRNever1 : {r:Nat} -> plus r r = 1 -> Void
plusRRNever1 {r = 0} Refl impossible
plusRRNever1 {r = (S 0)} Refl impossible
plusRRNever1 {r = (S (S k))} prf = ?somethingWrong
