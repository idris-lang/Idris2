infixr 5 ::

namespace List
    public export
    data List a = Nil | (::) a (List a)

namespace Stream
    public export
    data Stream a = (::) a (Inf (Stream a))

ones : Stream Integer
ones = num :: ones
  where
    num : Integer -- gratuitous where for a regression test!
    num = 1

data Nat = Z | S Nat

take : Nat -> Stream a -> List a
take Z xs = Nil
take (S k) (x :: xs) = List.(::) x (take k xs)

