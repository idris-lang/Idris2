data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> (1 xs : Vect k a) -> Vect (S k) a

partial
append : (1 _ : Vect n a) -> Vect m a -> Vect (n + m) a
append (x :: zs@(y :: ws)) ys = ?foo -- zs usable, y+ws not

cappend : (1 _ : Vect n a) -> Vect m a -> Vect (plus n m) $a
cappend xs ys
    = case xs of
           Nil => ys
           x :: zs => ?bar -- zs usable, xs not

cappend2 : (1 _ : Vect n a) -> Vect m a -> Vect (plus n m) a
cappend2 xs ys
    = case xs of
           Nil => ys
           x :: zs => let ts = zs in ?baz -- ts usable, xs+zs not
