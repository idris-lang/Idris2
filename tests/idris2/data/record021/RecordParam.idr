record Ok (ty : Type) where
  f : (x : ty) -> Type
record Fail (ty : Type) where
  f : {x : ty} -> Type
