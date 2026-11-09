import Language.Reflection

%language ElabReflection

record X (a : Type) where
  f : a

record Y a where
  f : a

data Z' : ?h1 -> Type where
  MkZ : t -> Z' t

f : ?h2 -> Type
f x = List x

out : List (Name, TTImp)
out = %runElab getType `{X}

out2 : List (Name, TTImp)
out2 = %runElab getType `{Y}

out3 : List (Name, TTImp)
out3 = %runElab getType `{Z'}

out4 : List (Name, TTImp)
out4 = %runElab getType `{Main.f}
