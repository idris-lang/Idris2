> data Vect : Nat -> Type -> Type where
>      Nil : Vect Z a
>      (::) : a -> Vect k a -> Vect (S k) a

> %name Vect xs, ys, zs

> transpose : {m : Nat} -> Vect n (Vect m a) -> Vect m (Vect n a)
> transpose [] = ?empties
> transpose (x :: xs) = let xs_trans = transpose xs in
>                           ?transposeHelper
