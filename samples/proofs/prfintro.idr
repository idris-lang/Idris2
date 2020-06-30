import Data.Vect

four_eq : 4 = 4
four_eq = Refl

-- four_eq_five : 4 = 5
-- four_eq_five = Refl

twoplustwo_eq_four : 2 + 2 = 4
twoplustwo_eq_four = Refl

plus_reduces_Z : (m : Nat) -> plus Z m = m
plus_reduces_Z m = Refl

plus_reduces_Sk : (k, m : Nat) -> plus (S k) m = S (plus k m)
plus_reduces_Sk k m = Refl

idris_not_php : Z = "Z"

vect_eq_length : (xs : Vect n a) -> (ys : Vect m a) -> (xs = ys) -> n = m
vect_eq_length xs xs Refl = Refl
