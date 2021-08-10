%default total

data F : Type where
  MkFix : ((0 g : Type -> Type) -> g === Not -> g F) -> F

yesF : Not F -> F
yesF nf = MkFix (\ g, Refl => nf)

notF : Not F
notF (MkFix f) =
  let g = f Not Refl in
  g (yesF g)

argh : Void
argh = notF (yesF notF)
