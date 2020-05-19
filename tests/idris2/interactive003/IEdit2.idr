data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

append : Vect n a -> Vect m a -> Vect (n + m) a
append xs ys
    = case xs of
           [] => ?bar_3
           (x :: zs) => ?bar_4

