main : IO ()
main = do
    printLn "Café"
    printLn "Cafe\769"
    printLn "Idris the magic 龍"
    putStrLn $ "length \"Café\" = " ++ show (Prelude.String.length "Café")
    putStrLn $ "length \"Cafe\769\" = " ++ show (Prelude.String.length "Cafe\769")
