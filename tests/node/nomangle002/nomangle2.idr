
%nomangle
continue : Int -> Int
continue x = x + 1

%nomangle "refc:break"
break : Int -> Int
break x = x + 1

main : IO ()
main = pure ()
