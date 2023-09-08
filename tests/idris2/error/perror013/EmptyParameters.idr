module EmptyParameters

parameters (m : Nat -> Type)

f : (y : Nat) -> m y -> Unit
f y my = ()
