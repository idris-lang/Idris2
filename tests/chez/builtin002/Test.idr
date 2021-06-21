natToInt : Nat -> Integer
natToInt Z = 0
natToInt (S k) = 1 + natToInt k

%builtin NaturalToInteger natToInt

intToNat : Integer -> Nat
intToNat i = if i <= 0
    then Z
    else S $ intToNat (i - 1)

%builtin IntegerToNatural intToNat

add : Nat -> Nat -> Nat
add Z y = y
add (S x) y = S (add x y)

%transform "add" add x y = intToNat (prim__add_Integer (natToInt x) (natToInt y))

main : IO ()
main = do
    printLn $ intToNat 3141592
    printLn $ intToNat 12345
    printLn $ add 100 1000
    printLn $ add 9566 7554
