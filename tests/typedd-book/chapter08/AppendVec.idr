import Data.Nat
import Data.Vect

append_nil : Vect m elt -> Vect (plus m 0) elt
append_nil {m} xs = rewrite plusZeroRightNeutral m in xs

append_xs : Vect (S (m + k)) elt -> Vect (plus m (S k)) elt
append_xs {m} {k} xs = rewrite sym (plusSuccRightSucc m k) in xs

append : Vect n elt -> Vect m elt -> Vect (m + n) elt
append [] ys = append_nil ys
append (x :: xs) ys = append_xs (x :: append xs ys)
