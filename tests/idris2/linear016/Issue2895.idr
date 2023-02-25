record Ty where
  constructor MkTy
  0 obj : Type

record TyProj (d: Ty) where
  constructor MkTyProj
  proj : d.obj

record Id (x : Type) where
  constructor MkId
  getId : x

DepLensToDepOptic :
  {c1 : TyProj (MkTy (Nat -> Type))} ->
  Id (proj c1 3) -> -- remove the Id works
  Type
DepLensToDepOptic (MkId b') = ?hu
