
record Ty where
  constructor MkTy
  0 obj : Type

record TyProj (d: Ty) where
  constructor MkTyProj
  proj : d.obj

DepLensToDepOptic :
  {c1 : TyProj (MkTy (Nat -> Type))} ->
  (proj c1 3) ->
  Type
DepLensToDepOptic =
   (\(b) => ?mmm)
