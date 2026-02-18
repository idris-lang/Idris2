%default total

g3 : (Nat, Nat) -> Nat
g3 (x, y) = x
g3 _ = 6

f : Monad m => m (Nat, Nat)

h3 : Monad m => m Nat
h3 = do
  (x, y) <- f
    | _ => pure 5
  pure x
