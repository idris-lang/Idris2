
typebind
Exists : (t : Type) -> (t -> Type) -> Type
Exists = DPair

val : Exists (n : Nat) | Vect n Nat
val = (4 ** [0,1,2,3])


