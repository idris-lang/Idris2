import System.File
import Data.Strings
import Data.List

-- read in a dictionary, shuffle and then resort

mylast : List a -> Maybe a
mylast [] = Nothing
mylast [x] = Just x
mylast (x::xs) = mylast xs

doSort : Nat -> IO ()
doSort Z     = putStrLn "Done"
doSort (S k) = do Right dict<-readFile "words"
                   | Left err => putStrLn $ show err
                  -- reverse and get last word
                  let xs  = reverse $ words dict
                  putStrLn $ show $ mylast xs
                  -- sort reversed list and get last word
                  putStrLn $ show $ mylast $ sort xs
                  doSort k

main : IO ()
main = do max <- getLine
          doSort (integerToNat (cast max))
