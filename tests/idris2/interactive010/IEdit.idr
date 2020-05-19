data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

dupAll : Vect n a -> Vect n (a, a)
dupAll xs = zipHere xs xs
  where
    zipHere : forall n . Vect n a -> Vect n b -> Vect n (a, b)

