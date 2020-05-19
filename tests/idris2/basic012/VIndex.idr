data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

-- Checking that we can access 'n' from the index even though it's
-- not explicitly brought into scope, and the match requires n to be
-- Z or S k...
vlen : {n : Nat} -> Vect n a -> Nat
vlen [] = n
vlen (x :: xs) = n
