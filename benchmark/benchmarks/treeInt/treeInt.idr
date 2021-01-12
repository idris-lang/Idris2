module Main

import BTree
import Data.List
import Data.Stream

treesort : Ord a => List a -> List a
treesort xs = BTree.toList $ toTree xs

lincong : Integer -> Stream Integer
lincong = tail . (iterate (\n => (1103515245 * (fromInteger n) + 12345) `mod` 2147483648))

randishInts : Nat -> Integer -> List Integer
randishInts size seed = take size $ lincong seed

mylast : List a -> Maybe a
mylast [] = Nothing
mylast [x] = Just x
mylast (x::xs) = mylast xs

doSort : Nat -> IO ()
doSort Z     = putStrLn "Done"
doSort (S k) = do let xs = treesort $ randishInts 30000 $ natToInteger k
                  -- get last elem to make sure compiler doesn't optimise away the sort
                  putStrLn $ show $ mylast xs
                  doSort k

main : IO ()
main = do max <- getLine
          doSort (integerToNat (cast max))
