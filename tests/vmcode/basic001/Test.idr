
foo : Either (Either () ()) () -> String
foo (Left (Left ())) = "Left Left"
foo (Left (Right ())) = "Left Right"
foo (Right ()) = "Right"

bah : List Nat -> Nat
bah [] = 0
bah (x :: xs) = x + bah xs

baz : Int -> Int
baz 10 = -1
baz _ = -2

main : IO ()
main = do
    -- primitives
    printLn $ the Int $ 10 + 11 * 92
    printLn $ the Bits32 $ 8 * 9 * 10
    printLn $ the Integer $ 19 * 19

    -- pattern matching
    putStrLn $ foo $ Left (Left ())
    putStrLn $ foo $ Right ()
    putStrLn $ foo $ Left (Right ())

    -- recursion
    printLn $ bah [0 .. 10]
    printLn $ bah [11, 2]

    -- primitive pattern matching
    printLn $ baz 10
    printLn $ baz (-100)
