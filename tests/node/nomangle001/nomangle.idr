
%nomangle
foo : Int -> Int
foo x = x + 1

%nomangle "$_baz"
baz : Int -> Int
baz x = x + 1

%nomangle
continue : Int -> Int
continue x = x + 1

main : IO ()
main = pure ()
