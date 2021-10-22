import Data.List.Alternating

main : IO ()
main = do
    let xs = the (Fence Double String) [1, "Hello", 2, "world", 3]
    let ys = the (Fence Double String) [1, "Hello", 0, "world", 3]

    printLn xs

    printLn $ xs == xs
    printLn $ xs == ys

    printLn $ compare xs xs == EQ
    printLn $ compare xs ys == GT

    printLn $ bimap (+ 1) (++ "!") xs

    printLn $ bifoldr (mapFst . avg) (mapSnd . join) (0, "") xs
    printLn $ bifoldl (flip $ mapFst . avg) (flip $ mapSnd . (flip join)) (0, "") xs

    ignore $ bitraverse printLn printLn xs

    printLn $ the (List String) $ forget $ mapFst show xs
  where
    avg : Double -> Double -> Double
    avg x y = (x + y) / 2

    join : String -> String -> String
    join "" t = t
    join s "" = s
    join s t = s ++ " " ++ t
