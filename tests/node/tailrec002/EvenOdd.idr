module Main

mutual
    is_even : Nat -> Bool
    is_even Z = True
    is_even (S k) = is_odd k

    is_odd : Nat -> Bool
    is_odd Z = False
    is_odd (S k) = is_even k

main : IO ()
main = printLn (is_even 10)
