data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

wrong : a -> Vect (S n) a -> Vect (S n) a
wrong xs = x :: ys
