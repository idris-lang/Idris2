%default total

-- This one needed withHoles on tcOnly (instead of withArgHoles)
-- or the solved implicit for the (ty : Type) on Maybe would not be
-- substituted.
length : Maybe (List a) -> Nat
length Nothing = 0
length (Just []) = 0
length (Just (x :: xs)) = 1 + length (Just xs)

one : List a -> Nat
one (x :: y :: zs) = one (x :: zs)
one _ = 0

two : List a -> Nat
two (a :: b :: c :: d :: es) = two (a :: c :: es)
two _ = 0

three : List a -> Nat
three (a :: b :: c :: d :: es) = three (b :: c :: es)
three _ = 0

failing "not total"
  four : List Nat -> Nat
  four (a :: b :: c :: es) = four (b :: c :: a :: es)
  four _ = 0

-- also needs withHoles
five : (List a, List a) -> List a
five (a :: as, bs) = a :: five (as, bs)
five ([], _) = []

-- This is total, but not supported
failing "not total"
  six : (List a, List a) -> List a
  six (a :: as, bs) = a :: six (bs, as)
  six ([], _) = []


failing "not total"
  -- If we didn't check all of the arguments of MkTuple for
  -- Same/Smaller, then this would be incorrectly accepted as total
  first : (List Nat, List Nat) -> Nat
  second : (List Nat, List Nat) -> Nat

  first (x :: xs, ys) = second (xs, Z :: ys)
  first _ = Z

  second (xs, y :: ys) = first (1 :: xs, ys)
  second _ = Z
