
data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

data Elem : a -> Vect n a -> Type where
     Here : Elem x (x :: xs)
     There : {xs : Vect n a} -> Elem x xs -> Elem x (y :: xs)

getIndex : Elem x xs -> Nat
getIndex Here = 0
getIndex (There p) = S (getIndex p)

Beatles : Vect ? String
Beatles = ["John", "Paul", "George", "Ringo"]

georgeInBeatles : Elem "George" Beatles
georgeInBeatles = There (There Here)
