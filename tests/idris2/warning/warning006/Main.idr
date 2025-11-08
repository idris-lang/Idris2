
import Data.Vect

-- fromInteger on LHS
head : (n : Nat) -> {auto 0 prf : IsSucc n} -> Vect n a -> a
head 0 _ impossible
head (S k) (x :: xs) = x

data Foo = Z | S Foo

-- No matching constuctor of a known type
head' : (n : Nat) -> {auto 0 prf : IsSucc n} -> (Foo,Foo) -> Vect n a -> a
head' Z Z _ impossible
head' (S k) _ (x :: xs) = x

-- Ambiguous constructor of unknown type
head'' : (n : Nat) -> {auto 0 prf : IsSucc n} -> (Foo,Foo) -> Vect n a -> a
head'' Z (Z,_) _ impossible
head'' (S k) _ (x :: xs) = x
