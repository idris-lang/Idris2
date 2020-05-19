foo : (Nat, Nat) -> Nat
foo (Z, Z) = Z

bar : {a : _} -> a -> Nat
bar Z = Z
bar (S _) = S Z

cty : (a : Type) -> a -> Nat
cty Nat Z = Z
cty Nat (S _) = S Z
cty _ x = S (S Z)

badBar : a -> Nat
badBar Z = Z
badBar (S _) = S Z
