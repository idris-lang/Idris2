data Nat = Z | S Nat

plus : Nat -> Nat -> Nat
plus Z     y = y
plus (S k) y = S (plus k y)

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     Cons : a -> Vect k a -> Vect (S k) a

foldl : (0 b : Nat -> Type) ->
        ({k : Nat} -> b k -> a -> b (S k)) ->
        b Z ->
        Vect n a -> b n
foldl b g z Nil = z
foldl b g z (Cons x xs) = foldl (\i => b (S i)) g (g z x) xs

reverse : Vect n a -> Vect n a
reverse
    = foldl (\m => Vect m a)
            (\rev => \x => Cons x rev) Nil

append : Vect n a -> Vect m a -> Vect (plus n m) a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

vlength : (n : Nat) -> Vect n a -> Nat
vlength Z Nil = Z
vlength n@_ (Cons x xs) = n -- (vlength _ xs);

zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f Nil Nil = Nil
-- zipWith f (Cons x xs) Nil impossible
zipWith f (Cons x xs) (Cons y ys) = Cons (f x y) (zipWith f xs ys)
