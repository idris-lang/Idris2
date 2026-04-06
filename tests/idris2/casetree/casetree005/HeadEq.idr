data D : Type where
  MkD : (DPair (Pair Unit Unit) (const Bool) -> Type) -> D

shape : D -> Type
shape (MkD _) = DPair (Pair Unit Unit) (const Bool)

position : (c : D) -> shape c -> Type
position (MkD p) s = p s

data Extension : (c : D) -> Type where
  MkExtension : (s : shape c) -> (payloads : position c s -> Unit) -> Extension c

Derivative : D
Derivative = MkD $ \(MkDPair s p) => (the (_ -> Type) (\(u1, u2) => Bool)) s

toPairSimple : Extension Derivative
toPairSimple =
    MkExtension (MkDPair ((), ()) True) $ \case
      True  => MkUnit
      False => MkUnit
