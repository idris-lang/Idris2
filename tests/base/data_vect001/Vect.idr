import Data.Vect

streams : List (Stream Int)
streams = [ rangeFrom 0
          , cycle [1, 3, 5]
          , iterate (*2) 1
          ]

firstFive : List (Vect 5 Int)
firstFive = map (take 5) streams

main : IO ()
main = do printLn firstFive