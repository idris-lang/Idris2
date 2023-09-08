natToInt : Nat -> Integer
natToInt Z = 0
natToInt (S k) = 1 + natToInt k

%builtin NaturalToInteger natToInt

lt : Nat -> Nat -> Bool
lt Z Z = False
lt Z _ = True
lt (S j) (S k) = lt j k
lt (S _) Z = False

%transform "lt" lt j k = intToBool (prim__lt_Integer (natToInt j) (natToInt k))

main : IO ()
main = do
    printLn $ natToInt 3141592
    printLn $ natToInt 12345
    printLn $ lt 100 1000
    printLn $ lt 9566 7554
