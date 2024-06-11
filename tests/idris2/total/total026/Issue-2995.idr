-- see https://github.com/idris-lang/Idris2/issues/2995

%default total

%tcinline
incAll : Stream Nat -> Stream Nat
incAll (x::xs) = S x :: incAll xs

%tcinline
incAll' : Stream Nat -> Stream Nat
incAll' = \(x::xs) => S x :: incAll' xs

%tcinline
incAll'' : Stream Nat -> Stream Nat
incAll'' = \ys => case ys of
    (x :: xs) => S x :: incAll'' xs
