%default total

data Desc : Type where
  Prod : (d, e : Desc) -> Desc
  Rec : Desc

Elem : (d : Desc) -> Type -> Type
Elem (Prod d e) x = (Elem d x, Elem e x)
Elem Rec x = x

failing "Mu is not total, not strictly positive"

  data Mu : Desc -> Type where
    MkMu : Elem d (Mu d) -> Mu d

data Mu : Desc -> Type where
  MkMu : Elem d (assert_total (Mu d)) -> Mu d
