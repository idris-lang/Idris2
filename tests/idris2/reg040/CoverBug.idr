module CoverBug

import Data.So

public export
data FastNat : Type where
  MkFastNat : (val : Integer) -> {auto 0 prf : So True} -> FastNat

prv1 : Integer -> (x : Integer ** So $ True)
prv1 x =
  case choose True of
    Left prf => (x ** Oh)
    Right noprf => absurd noprf

fromInteger : Integer -> FastNat
fromInteger v =
  let (v ** p) = prv1 $ v
  in MkFastNat v

doit : FastNat -> FastNat
doit 0 = 0
