data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

transposeHelper : Vect m a -> (1 xs_trans : Vect m (Vect k a)) -> Vect m (Vect (S k) a)
