%default partial

foo : Maybe a -> a
foo (Just x) = x

data Vect : ? -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

data Fin : Nat -> Type where
     FZ : Fin (S k)
     FS : Fin k -> Fin (S k)

lookup : Fin n -> Vect n a -> a
lookup FZ (x :: xs) = x
lookup (FS k) (x :: xs) = lookup k xs

lookup' : Fin n -> Vect n a -> a
lookup' (FS k) (x :: xs) = lookup' k xs

lookup'' : Fin n -> Vect n a -> a
lookup'' n xs = lookup' n xs

main : IO ()
main = do let x = foo Nothing
          printLn (the Int x)
