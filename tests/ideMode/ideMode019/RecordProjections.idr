record Pack (a : Type) where
  constructor MkPack
  nested : a
  nat : Nat

proj : List (Pack Bool) -> List (Bool, Nat)
proj []        = []
proj (x :: xs) = MkPair x.nested (nat x) :: proj xs

ununpack : List (Pack (Pack a)) -> List a
ununpack = map (.nested.nested)

deepNats : List (Pack (Pack a)) -> List Nat
deepNats = map ((.nat) . (.nested))
