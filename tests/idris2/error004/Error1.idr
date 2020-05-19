import Data.List

data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

wrong : String
wrong = show (the (Vect _ _) [1,2,3,4])
