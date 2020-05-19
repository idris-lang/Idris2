data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

comp : (a -> b) -> (b -> c) -> a -> c
comp = ?baz

zipWith : (a -> b -> c) -> (1 xs : Vect n a) -> (1 ys : Vect n b) -> Vect n c
zipWith f [] [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

transposeHelper : Vect m a -> (1 xs_trans : Vect m (Vect k a)) -> Vect m (Vect (S k) a)
transposeHelper xs ys = zipWith ?foo xs ys
