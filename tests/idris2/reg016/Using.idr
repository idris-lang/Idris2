module Using

interface MagmaT a where
  op: a -> a -> a

interface MagmaT a => SemigroupT a where
  assoc: (x, y, z: a) -> (x `op` y) `op` z = x `op` (y `op` z)

[NamedMagma1] MagmaT Bool where
  False `op` False = False
  _     `op` _     = True

[NamedMagma2] MagmaT Bool where
  True `op` True = True
  _    `op` _    = False

[NamedSemigroup1] SemigroupT Bool using NamedMagma1 where
  assoc = ?hole1

[NamedSemigroup2] SemigroupT Bool using NamedMagma2 where
  assoc = ?hole2
