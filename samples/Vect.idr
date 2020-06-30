data Vect : Nat -> Type -> Type where
   Nil  : Vect Z a
   (::) : a -> Vect k a -> Vect (S k) a

(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

data Fin : Nat -> Type where
   FZ : Fin (S k)
   FS : Fin k -> Fin (S k)

index : Fin n -> Vect n a -> a
index FZ     (x :: xs) = x
index (FS k) (x :: xs) = index k xs

filter : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter p Nil = (_ ** [])
filter p (x :: xs)
    = case filter p xs of
           (_ ** xs') => if p x then (_ ** x :: xs')
                                else (_ ** xs')

cons : t -> (x : Nat ** Vect x t) -> (x : Nat ** Vect x t)
cons val xs
    = record { fst = S (fst xs),
               snd = (val :: snd xs) } xs

cons' : t -> (x : Nat ** Vect x t) -> (x : Nat ** Vect x t)
cons' val
    = record { fst $= S,
               snd $= (val ::) }

Show a => Show (Vect n a) where
    show xs = "[" ++ show' xs ++ "]" where
        show' : forall n . Vect n a -> String
        show' Nil        = ""
        show' (x :: Nil) = show x
        show' (x :: xs)  = show x ++ ", " ++ show' xs

