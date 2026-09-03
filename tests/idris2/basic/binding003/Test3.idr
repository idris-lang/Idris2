

autobind
for : List a -> (a -> IO ()) -> IO ()

range : List Nat
range = [1 .. 10]

main : IO ()
main = for (x : range) | printLn x
