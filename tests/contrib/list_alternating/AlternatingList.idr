import Data.List.Alternating

main : IO ()
main = do
    let xs = the (Odd Double String) [1, "Hello", 2, "world", 3]
    let ys = the (Odd Double String) [1, "Hello", 0, "world", 3]

    printLn xs

    printLn $ xs == xs
    printLn $ xs == ys

    printLn $ compare xs xs == EQ
    printLn $ compare xs ys == GT

    printLn $ bimap (+ 1) (++ "!") xs

    printLn $ bifoldr (mapFst . avg) (mapSnd . join) (0, "") xs
    printLn $ bifoldl (flip $ mapFst . avg) (flip $ mapSnd . (flip join)) (0, "") xs

    ignore $ bitraverse printLn printLn xs

    printLn $ map (++ "!") xs

    printLn $ the (Odd Double String) $ [1, "Hello"] ++ [2, "world", 3]
    printLn $ the (Odd Double String) $ [1, "Hello", 2] ++ ["world", 3]

    let us = the (Odd String Double) ["Hello", 0, "world", 1, "!"]
    let vs = the (Odd String Double) ["Lorem", 1, "ipsum"]

    printLn $ us <+> vs
    printLn $ us +> "!"
    printLn $ "Oh, " <+ us
    printLn $ the (Odd String Double) neutral

    printLn $ foldr avg 0 us
    printLn $ foldl avg 0 us

    printLn $ the (Odd String Double) $ pure 1
    printLn $ the (Odd String Double) $ ["Hello", (+1), "world", (+10), "!"] <*> ["Lorem", 1, "ipsum", 2, "."]

    printLn $ the (Odd String Double) empty
    printLn $ us <|> vs

    printLn $ Snd.do
        x <- the (Odd String Double) ["Hello", 1, "world", 2, "!"]
        [",", x + 1, " "]

    printLn $ Fst.do
        x <- the (Odd String Double) ["Hello", 1, "world", 2, "!"]
        ["Um,", 3, x]

    ignore $ traverse printLn us

    printLn $ odds xs
    printLn $ evens xs
    printLn $ the (List String) $ forget $ mapFst show xs
  where
    avg : Double -> Double -> Double
    avg x y = (x + y) / 2

    join : String -> String -> String
    join "" t = t
    join s "" = s
    join s t = s ++ " " ++ t
