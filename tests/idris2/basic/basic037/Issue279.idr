module Main

{-- comment 1 --}

someFunction : IO ()

{-- comment 2 --}

main : IO ()
main = do
    someFunction
    pure ()
