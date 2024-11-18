module WithProof1

%default total

%hide List.filter

filter : (p : a -> Bool) -> (xs : List a) -> List a
filter p [] = []
filter p (x :: xs) with (p x)
  filter p (x :: xs) | False = filter p xs
  filter p (x :: xs) | True = x :: filter p xs

consumeEq : (1 _ : x === y) -> ()
consumeEq Refl = ()

filterSquared : (p : a -> Bool) -> (xs : List a) ->
                filter p (filter p xs) === filter p xs
filterSquared p [] = Refl
filterSquared p (x :: xs) with (p x) proof 1 eq
  filterSquared p (x :: xs) | False = case consumeEq eq of
    () => filterSquared p xs
  filterSquared p (x :: xs) | True = case consumeEq eq of
    () => rewrite eq in cong (x ::) (filterSquared p xs)
