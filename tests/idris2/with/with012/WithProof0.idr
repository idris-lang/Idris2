module WithProof0

%default total

%hide List.filter

filter : (p : a -> Bool) -> (xs : List a) -> List a
filter p [] = []
filter p (x :: xs) with (p x)
  filter p (x :: xs) | False = filter p xs
  filter p (x :: xs) | True = x :: filter p xs


filterSquared : (p : a -> Bool) -> (xs : List a) ->
                filter p (filter p xs) === filter p xs
filterSquared p [] = Refl
filterSquared p (x :: xs) with (p x) proof 0 eq
  filterSquared p (x :: xs) | False = filterSquared p xs -- easy
  filterSquared p (x :: xs) | True
    = rewrite eq in cong (x ::) (filterSquared p xs)
