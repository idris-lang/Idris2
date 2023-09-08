module NestedWith

%default total

interface DecEq a where
  decEq : (x, y : a) -> Dec (x === y)

(DecEq a, DecEq b) => DecEq (a, b) where
  decEq (x, y) (a, b) with (decEq x a) | (decEq y b)
    _ | Yes eqL | Yes eqR = Yes (cong2 (,) eqL eqR)
    _ | No neqL | _ = No $ \prf => neqL $ cong fst prf
    _ | _ | No neqR = No $ \prf => neqR $ cong snd prf
