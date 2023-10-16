%default total

f : (xs : List Int) -> (y : Int) -> (ys : List Int) -> Maybe (xs === y :: ys) -> Unit
f [] _ _ Nothing = ()
f (x :: xs) y ys Nothing = f xs y ys Nothing
f .(y :: ys) y ys (Just Refl) = f ys y ys Nothing
