%default total

data E : Type -> Type -> Type where
  L : a -> E a b

data X : Type where
  MkX : (DPair Unit (\MkUnit => E Unit Nat) -> Type) -> X

getShape : (c : X) -> Type
getShape (MkX _) = DPair Unit (\MkUnit => E Unit Nat)

getPayloads : (c : X) -> getShape c -> Type
getPayloads (MkX p) = p

data Extension : (c : X) -> Type where
  MkExtension :
    (shape : getShape c) ->
    (payloads : getPayloads c shape -> Unit) ->
    Extension c

Derivative : X
Derivative = MkX (\(MkDPair MkUnit _) => E Unit Nat)

toPairSimple : Extension Derivative
toPairSimple = MkExtension (MkDPair () (L MkUnit)) $ \(L a) => a
