module WithProof1Fail

%default total

%hide List.filter

filter : (p : a -> Bool) -> (xs : List a) -> List a
filter p [] = []
filter p (x :: xs) with (p x)
  filter p (x :: xs) | False = filter p xs
  filter p (x :: xs) | True = x :: filter p xs

failing "While processing right hand side of with block in filterSquared. There are 0 uses of linear name eq"
  filterSquared : (p : a -> Bool) -> (xs : List a) ->
                  filter p (filter p xs) === filter p xs
  filterSquared p [] = Refl
  filterSquared p (x :: xs) with (p x) proof 1 eq
    filterSquared p (x :: xs) | False = filterSquared p xs
    filterSquared p (x :: xs) | True = filterSquared p xs
