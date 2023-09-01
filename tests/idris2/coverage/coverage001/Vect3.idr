
%default partial

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

zip : Vect n a -> Vect n b -> Vect n (a, b)
zip [] Z impossible
zip [] [] = Nil
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
