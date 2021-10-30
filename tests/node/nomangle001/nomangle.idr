
%nomangle
foo : Int -> Int
foo x = x + 1

%nomangle "$_baz"
baz : Int -> Int
baz x = x + 1

%nomangle "refc:idr_another_name"
          "javascript:another_name"
anotherName : Int -> Int
anotherName x = x + 1

main : IO ()
main = pure ()
