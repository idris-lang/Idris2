infixr 5 ::

data List a = Nil | (::) a (List a)
data Nat = Z | S Nat

data Vect : Type -> Type where
data Set : Type -> Type where

namespace Vect
  export
  toList : Vect a -> List a
  export
  fromList : List a -> Vect a

namespace Set
  export
  toList : Set a -> List a
  export
  fromList : List a -> Set a

keepUnique : List b -> List b
keepUnique {b} xs = toList (fromList xs)

