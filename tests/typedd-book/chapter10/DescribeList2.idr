data ListLast : List a -> Type where
     Empty : ListLast []
     NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          NonEmpty xs y => NonEmpty (x :: xs) y

describe_list_end : List Int -> String

describe_list_end input with (listLast input)
  describe_list_end [] | Empty = ?describe_list_end_rhs_1
  describe_list_end (xs ++ [x]) | (NonEmpty xs x) = ?describe_list_end_rhs_2
