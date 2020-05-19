import Data.List

data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

Show a => Show (Vect n a) where
  show [] = "END"
  show (x :: xs) = show x ++ ", " ++ show xs

Show (Vect n Integer) where
  show [] = "END"
  show (x :: xs) = show x ++ ", " ++ show xs

wrong : String
wrong = show (the (Vect _ _) [1])
