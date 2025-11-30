fn : (x : Bool) -> if x then (Nat -> Nat) else Void
fn True x = x

f2 : Void
f2 = fn False
