data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

append : Vect n a -> Vect m a -> Vect (n + m) a
append {n} xs ys = ?foo

vadd : Num a => Vect n a -> Vect n a -> Vect n a
vadd [] ys = ?bar
vadd (x :: xs) ys = ?baz

suc : (x : Nat) -> (y : Nat) -> x = y -> S x = S y
suc x y prf = ?quux

suc' : x = y -> S x = S y
suc' {x} {y} prf = ?quuz

