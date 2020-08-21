foo : String
foo = "ällo"

ällo : Int
ällo = 42

main : IO ()
main = do printLn ällo
          putStrLn "ällo"
