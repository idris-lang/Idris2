data Duo : List a -> Type where
     MkDuo : {left, right : List a} ->
             Duo (left ++ right)

unconsView : (xs : List a) -> Duo xs
unconsView []        = MkDuo {left = []} {right = []}
unconsView (x :: xs) = MkDuo {left = [x]} {right = xs}

getTail : (xs : List a) -> List a
getTail xs with (unconsView xs)
  getTail (left ++ right) | MkDuo {left} {right} = right
