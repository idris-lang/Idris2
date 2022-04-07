module NestedWith

%default total

interface DecEq a where
  decEq : (x, y : a) -> Dec (x === y)

(DecEq a, DecEq b) => DecEq (a, b) where
  decEq (x, y) (a, b) with (decEq x a) | (decEq y b)
    _ | Yes eqL | Yes eqR = Yes (cong2 (,) eqL eqR)
    _ | No neqL | _ = No (neqL . cong fst)
    _ | _ | No neqR = No (neqR . cong snd)
