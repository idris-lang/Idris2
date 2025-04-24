import M0
import M1

public export
Scoped : Type
Scoped = List Name -> SnocList Name -> Type

data A2bs : Scoped -> Scoped where
  Mk2Abs : (x : Name) -> t f (g :< x) -> A2bs t f g

partial
Eq (A2bs t f g) where
  Mk2Abs  x@_ b == Mk2Abs x' b' with (decEq x x')
    _ | _ = False
