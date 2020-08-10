data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

my_cong : forall f . (x : a) -> (y : a) -> x = y -> f x = f y

append : Vect n a -> Vect m a -> Vect (n + m) a

lappend : (1 _ : List a) -> (1 _ : List a) -> List a

lappend1 : List a -> List a -> List a

lappend2 : List a -> List a -> List a
lappend2 [] ys = ?lappend2_rhs_1
lappend2 (x :: xs) ys = ?lappend2_rhs_2
