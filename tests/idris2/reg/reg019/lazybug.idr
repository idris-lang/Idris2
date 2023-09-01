bools : List Bool
bools = [True, False]

main : IO ()
main = printLn $ or (map id bools)

main2 : IO ()
main2 = printLn $ or (map (\x => x) bools)

main3 : IO ()
main3 = printLn $ or (map (\x => Delay x) bools)

main4 : IO ()
main4 = printLn $ or bools
