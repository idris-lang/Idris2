module WithProof

%default total

filter : (p : a -> Bool) -> (xs : List a) -> List a
filter p [] = []
filter p (x :: xs) with (p x)
  filter p (x :: xs) | False = filter p xs
  filter p (x :: xs) | True = x :: filter p xs


filterSquared : (p : a -> Bool) -> (xs : List a) ->
                filter p (filter p xs) === filter p xs
filterSquared p [] = Refl
{-
filterSquared p (x :: xs) with (p x)
  filterSquared p (x :: xs) | False = filterSquared p xs -- easy
  filterSquared p (x :: xs) | True = ?a
     -- argh! stuck on another with-block casing on (p x)!
     -- we could check (p x) again but how do we prove it
     -- can only ever be `True`?!
-}
filterSquared p (x :: xs) with (p x) proof eq
  filterSquared p (x :: xs) | False = filterSquared p xs -- easy
  filterSquared p (x :: xs) | True
    = rewrite eq in cong (x ::) (filterSquared p xs)
