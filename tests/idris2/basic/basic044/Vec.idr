module Vec

import Data.Fin

%default total

%logging 1
%logging "declare.def" 2

Vec : Type -> Nat -> Type
Vec a n = Fin n -> a

Nil : Vec a Z
Nil = absurd

(::) : a -> Vec a n -> Vec a (S n)
(x :: xs) FZ = x
(x :: xs) (FS i) = xs i

test : Vec (List Nat) 2
test = [[], [0]]
