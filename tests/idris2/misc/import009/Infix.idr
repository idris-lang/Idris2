module Infix

export
infix 6 !!

(!!) : List a -> Nat -> Maybe a
[] !! _ = Nothing
(x :: _) !! Z = Just x
(_ :: xs) !! (S n) = xs !! n
