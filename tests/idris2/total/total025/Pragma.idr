%default total

%totality_depth 1

failing "not total"
  one : List a -> Nat
  one (a :: b :: c :: es) = one (a :: b :: es)
  one _ = 0

%totality_depth 3

two : List a -> Nat
two (a :: b :: c :: es) = two (a :: b :: es)
two _ = 0
