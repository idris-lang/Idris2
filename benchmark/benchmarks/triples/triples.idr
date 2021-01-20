module Main

triples : Int -> List (Int, Int, Int)
triples top = [(x,y,z) | z<-[1..top], y<-[1..z], x<-[1..y],
                         x * x + y * y == z * z ]

main : IO ()
main = do putStrLn "Max: "
          max <- getLine
          printLn (triples (cast max))
