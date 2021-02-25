%default total

||| View for traversing a list backwards
public export
data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : (x : a) -> (xs : List a) ->
            (rec : SnocList xs) -> SnocList (xs ++ [x])

empty : SnocList (x :: xs) -> a
empty Empty impossible


snoc : SnocList (x :: xs) -> a
snoc (Snoc _ _ _) impossible
