module Data.List.Extra

%default covering

||| Fetches the element at a given position.
||| Returns `Nothing` if the position beyond the list's end.
public export
elemAt : List a -> Nat -> Maybe a
elemAt []        _     = Nothing
elemAt (l :: _)  Z     = Just l
elemAt (_ :: ls) (S n) = elemAt ls n
