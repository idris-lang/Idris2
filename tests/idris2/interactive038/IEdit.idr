data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

replicate : {m : Nat} -> a -> Vect m a

transpose : {m : Nat} -> Vect n (Vect m a) -> Vect m (Vect n a)
transpose [] = ?transpose_rhs_1
transpose (x :: xs) = ?transpose_rhs_2
