-- %logging 2
test : List a -> Nat -> Nat
test xs n
    = case xs of
           [] => Z
           (y :: ys) => case n of
                             Z => Z
                             (S k) => calculate xs k
  where
    calculate : List a -> Nat -> Nat
%logging 0
