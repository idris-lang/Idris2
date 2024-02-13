module LazyIsStillThere

topLevelConst : Nat
topLevelConst = 16 + 8

main : IO ()
main = putStrLn "Top-level constant: \{show topLevelConst}"
