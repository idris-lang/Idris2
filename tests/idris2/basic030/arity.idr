data MyN = MkN Nat Nat

foo : Nat -> Nat -> Nat
foo x y = case MkN x of
               MkN z => y

main : IO ()
main = printLn (foo 2 2)
