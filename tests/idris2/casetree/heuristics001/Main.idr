-- Example from https://github.com/idris-lang/Idris2/pull/1448
mergeLim : List a -> List a -> Nat -> List a
mergeLim xs ys 0 = xs
mergeLim [] ys (S k) = ys
mergeLim xs [] (S k) = xs
mergeLim (x :: xs) (y :: ys) (S k) = x :: mergeLim xs (y :: ys) k
