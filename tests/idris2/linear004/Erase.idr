import Stuff

efn : ((0 x : Nat) -> Nat -> Nat) -> Nat
efn f = f (S Z) (S Z)

okfn : ((x : Nat) -> Nat -> Nat) -> Nat
okfn f = f (S Z) (S Z)

ignore : (0 x : Nat) -> Nat -> Nat
ignore x y = y

lin : (1 x : Nat) -> Nat -> Nat
lin x y = S x
