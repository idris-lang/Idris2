%default total

transport : a === b -> a -> b
transport Refl x = x

transportRev : a === b -> b -> a
transportRev Refl x = x

data D : Type where
  MkD : Nat -> Nat -> D

P : D -> Type
P (MkD (S _) _) = Void
P (MkD _ (S (S _))) = Void
P (MkD 0 0) = ()
P (MkD 0 1) = ()

lem : (n : Nat) -> P (MkD n (S (S m))) === Void
lem 0 = Refl
lem (S n) = Refl

mutual
  f : (x : D) -> P x
  -- The loop:
  f (MkD (S n) _) = transport (lem n) (g (MkD n))       -- this call to g is fishy!
  f (MkD n (S (S m))) = transportRev (lem n) (f (MkD (S n) m))
  -- Base cases:
  f (MkD 0 0) = ()
  f (MkD 0 1) = ()

  g : (h : Nat -> D) -> P (h 2)
  g h = f (h 2)

loop : Void
loop = f (MkD 1 0)
