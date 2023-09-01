%default total

data Fix : (Type -> Type) -> Type where
  MkFix : f (Fix f) -> Fix f

F : Type
F = Fix Not

yesF : Not F -> F
yesF nf = MkFix nf

notF : Not F
notF (MkFix f) = f (yesF f)

argh : Void
argh = notF (yesF notF)
