data X : Type -> Type where
  MkX : (a : Type) -> X a

f : X Nat -> ()
f (MkX Type) impossible
f (MkX String) impossible
f (MkX (List Bool)) impossible
f (MkX Nat) = ()
