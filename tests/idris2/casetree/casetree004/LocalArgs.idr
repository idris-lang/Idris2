import Data.Vect

bar : (f : List a -> Nat) -> (xs : List a) -> Nat
bar f xs = f xs

-- Idris was putting fx@f for the first implicit (instead of fx@(f xs))
foo : (f : List a -> Nat) -> (xs : List a) -> (0 _ : fx = f xs) -> Nat
foo f xs Refl = bar f xs

blah : (xs : List a) -> Vect (foo List.length xs Refl) ()
blah xs = replicate (length xs) ()
