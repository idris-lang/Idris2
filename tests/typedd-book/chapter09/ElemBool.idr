data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

elem : Eq a => (value : a) -> (xs : Vect n a) -> Bool
elem value [] = False
elem value (x :: xs) = case value == x of
                            False => elem value xs
                            True => True
