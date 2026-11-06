
length : List a -> Nat
length [] = ?hole1
length (x :: xs) = ?hole2

subtract : Nat -> Nat -> Nat
subtract Z _ = ?hole3
subtract (S n) _ = ?hole4

namespace Nested

  add : Nat -> Nat -> Nat
  add Z n = n
  add (S n) m = ?hole4
