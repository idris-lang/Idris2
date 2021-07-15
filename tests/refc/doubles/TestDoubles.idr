module TestDoubles

put : Double -> IO ()
put = putStrLn . show

main : IO ()
main = do
    put $ exp 1
    put $ log 1

    put $ sin 1
    put $ cos 1
    put $ tan 1
    put $ asin 1
    put $ acos 1
    put $ atan 1

    put $ sqrt 2

    put $ floor 1.5
    put $ ceiling 1.5
