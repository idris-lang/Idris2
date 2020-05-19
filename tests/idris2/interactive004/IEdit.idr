data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

curry : ((a, b) -> c) -> a -> b -> c
curry f x y = ?curry_rhs

uncurry : (a -> b -> c) -> (a, b) -> c
uncurry f x = ?uncurry_rhs

append : Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ?append_rhs_1
append (x :: xs) ys = ?append_rhs_2

zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f [] [] = ?zipWith_rhs_1
zipWith f (x :: xs) (y :: ys) = ?zipWith_rhs_2
