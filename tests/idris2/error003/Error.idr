import Data.List

data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

length : Vect n a -> Nat
length [] = Z
length (x :: xs) = S (length xs)

wrong : Nat -> Nat
wrong x = length x
