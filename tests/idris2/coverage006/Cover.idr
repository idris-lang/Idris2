import Data.Fin

data NNat = NZ | NS NNat

zsym : (x : NNat) -> x = NZ -> NZ = x
zsym NZ Refl = Refl
zsym (NS _) Refl impossible

zsym' : (x : NNat) -> x = NZ -> NZ = x
zsym' NZ Refl = Refl

foo : Nat -> String
foo 0 = "zero"
foo 1 = "one"
foo x = "something else"

bar : Fin (S (S (S Z))) -> String
bar 0 = "a"
bar 1 = "b"
bar 2 = "c"
