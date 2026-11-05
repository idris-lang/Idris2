foo : (0 _ : ()) -> Int
foo _ = 42

bar : (0 _ : ()) -> Int
bar = foo

main : IO ()
main = printLn $ bar ()
