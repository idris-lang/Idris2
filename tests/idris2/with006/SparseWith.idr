%hide List.filter

filter : (p : a -> Bool) -> List a -> List a
filter p []        = []
filter p (x :: xs) with (p x)
  _ | True  = x :: filter p xs
  _ | False = filter p xs

filterFilter : (p : a -> Bool) -> (xs : List a) ->
               filter p (filter p xs) === filter p xs
filterFilter p []        = Refl
filterFilter p (x :: xs) with (p x) proof eq
  _ | False = filterFilter p xs
  _ | True  with (p x)
    _ | True = cong (x ::) (filterFilter p xs)
