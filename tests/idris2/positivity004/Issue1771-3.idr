%default total

data Wrap : Type -> Type where
  MkWrap : a -> Wrap a

unwrap : Wrap a -> a
unwrap (MkWrap v) = v

data F : Type where
  MkF : Wrap (Not F) -> F

yesF : Not F -> F
yesF = MkF . MkWrap

notF : Not F
notF (MkF f) = unwrap f (yesF $ unwrap f)

argh : Void
argh = notF (yesF notF)
