count : Nat -> Stream Nat
count n = n :: count (S n)

badCount : Nat -> Stream Nat
badCount n = n :: map S (badCount n)

data SP : Type -> Type -> Type where
  Get : (a -> SP a b) -> SP a b
  Put : b -> Inf (SP a b) -> SP a b

copy : SP a a
copy = Get (\x => Put x copy)

process : SP a b -> Stream a -> Stream b
process (Get f) (x :: xs) = process (f x) xs
process (Put b sp) xs = b :: process sp xs

badProcess : SP a b -> Stream a -> Stream b
badProcess (Get f) (x :: xs) = badProcess (f x) xs
badProcess (Put b sp) xs = badProcess sp xs

doubleInt : SP Nat Integer
doubleInt = Get (\x => Put (the Integer (cast x))
                        (Put (the Integer (cast x) * 2) doubleInt))

countStream : Nat -> Stream Nat
countStream x = x :: countStream (x + 1)

main : IO ()
main = printLn (take 10 (process doubleInt (countStream 1)))
