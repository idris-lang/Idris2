%default total

data View : Nat -> Type where
  Plus : (k, l : Nat) -> View (k + l)

view : View m -> Void
view {m = %search} v impossible

argh : Void
argh = view (Plus Z Z)
