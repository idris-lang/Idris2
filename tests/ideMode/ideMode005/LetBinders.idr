module LetBinders

private infix 1 :::
record List1 (a : Type) where
  constructor (:::)
  head : a
  tail : List a

swap : List1 a -> List1 a
swap aas =
  let (a ::: as) := aas in
  let (b :: bs) = as
        | [] => a ::: []
      rest = a :: bs
  in b ::: rest

identity : List (Nat, a) -> List (List a)
identity =
  let

    replicate : (n : Nat) -> a -> List a
    replicate Z a = []
    replicate (S n) a = a :: replicate n a

    closure := uncurry replicate

  in map closure
