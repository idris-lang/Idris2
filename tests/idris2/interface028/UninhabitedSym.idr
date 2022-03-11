module UninhabitedSym

data MyNat = ZZ | SS MyNat

Uninhabited (ZZ = SS n) where
  uninhabited Refl impossible

Uninhabited (a = b) => Uninhabited (SS a = SS b) where
  uninhabited Refl @{ab} = uninhabited @{ab} Refl

%defaulthint
Uninhabited (x = y) => Uninhabited (y = x) where
  uninhabited = \h => void $ uninhabited $ sym h

find : Uninhabited (SS (SS ZZ) === SS ZZ)
find = %search
