module Data.Desc

public export
data Desc : (i : Type) -> Type where
  Say : i -> Desc i
  Sig : (s : Type) -> (d : s -> Desc i) -> Desc i
  Ask : i -> Desc i -> Desc i

public export
pure : Desc i -> (i -> Type) -> i -> Type
pure (Say x) f y = x === y
pure (Sig s d) f y = DPair s $ \s' => pure (d s') f y
pure (Ask x z) f y = DPair (f x) (\_ => pure z f y)

public export
data Data : Desc i -> i -> Type where
  Val : pure d (Data d) iv -> Data d iv

public export
(.getVal) : Data d i -> pure d (Data d) i
(.getVal) (Val x) = x
