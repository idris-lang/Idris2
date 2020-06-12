import Data.IOArray

main : IO ()
main
    = do x <- newArray 20
         writeArray x 10 "Hello"
         writeArray x 11 "World"
         printLn !(toList x)

         y <- fromList (map Just [1,2,3,4,5])
         printLn !(toList y)
