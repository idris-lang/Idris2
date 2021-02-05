module Libraries.Data.List.Extra

%default total

||| Fetches the element at a given position.
||| Returns `Nothing` if the position beyond the list's end.
public export
elemAt : List a -> Nat -> Maybe a
elemAt []        _     = Nothing
elemAt (l :: _)  Z     = Just l
elemAt (_ :: ls) (S n) = elemAt ls n

export
firstBy : (a -> Maybe b) -> List a -> Maybe b
firstBy p [] = Nothing
firstBy p (x :: xs)
  = case p x of
      Nothing => firstBy p xs
      Just win => pure win
