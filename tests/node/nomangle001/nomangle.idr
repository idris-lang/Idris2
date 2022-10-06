%nomangle "javascript:foo"
foo : Int -> Int
foo x = x

%nomangle "node:$_baz"
baz : Int -> Int
baz x = x

%nomangle "refc:idr_another_name"
          "javascript:another_name"
anotherName : Int -> Int
anotherName x = x

main : IO ()
main = pure ()
