plus2 : Nat -> Nat
plus2 = S . S

okplus2Injective : (x, y : Nat) -> Equal (plus2 x) (plus2 y) -> Equal x y
okplus2Injective Z Z Refl = Refl
okplus2Injective (S n) (S n) Refl = Refl
okplus2Injective Z (S _) _ impossible
okplus2Injective (S _) Z _ impossible

badplus2Injective : (x, y : Nat) -> Equal (plus2 x) (plus2 y) -> Equal x y
badplus2Injective Z Z Refl = Refl
badplus2Injective Z (S _) _ impossible
badplus2Injective (S _) Z _ impossible
badplus2Injective (S n) (S n) Refl = Refl
