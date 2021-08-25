import Data.Vect

streams : List (Stream Int)
streams = [ rangeFrom 0
          , cycle [1, 3, 5]
          , iterate (*2) 1
          ]

testTakeFromStream : List (Vect 5 Int)
testTakeFromStream = map (take 5) streams

main : IO ()
main = do printLn testTakeFromStream
