data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

append : Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ys
-- append (x :: xs) ys = x :: append xs ys

data Fin : Nat -> Type where
     FZ : Fin (S k)
     FS : Fin k -> Fin (S k)

lookup : Fin n -> Vect n a -> a
lookup FZ (x :: xs) = x
lookup (FS k) (x :: xs) = lookup k xs

zip : Vect n a -> Vect n b -> Vect n (a, b)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

