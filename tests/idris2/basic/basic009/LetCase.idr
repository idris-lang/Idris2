import Stuff

data IsSuc : Nat -> Type where
     Yes : IsSuc (S x)

pred : (x : Nat) -> IsSuc x -> Nat
pred (S x) Yes = x

test1 : Nat -> Nat
test1 x = let y = S (S x) in
              case x of
                   res => pred y ?foo

-- Propagating let binding's computational behaviour through case is
-- not supported, sorry!
{-
data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

test2 : Nat -> Nat -> Nat
test2 x@(S Z) y
    = case y of
           res =>
               let fn : Vect (S Z) Nat -> Nat
                   fn ys = ?bar
               in pred x Yes
-}
