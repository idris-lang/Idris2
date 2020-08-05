module Utils.Either

%default total

export
mapError : (a -> c) -> Either a b -> Either c b
mapError f e = either (Left . f) (Right . id) e

export
partitionEithers : List (Either a b) -> (List a, List b)
partitionEithers [] = ([], [])
partitionEithers (Left x :: es)
        = let (ls, rs) = partitionEithers es in
              (x :: ls, rs)
partitionEithers (Right y :: es)
        = let (ls, rs) = partitionEithers es in
              (ls, y :: rs)
