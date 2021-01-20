import Data.List
import Data.Stream

-- the built in sort function is an implementation of merge sort (for now at least)

lincong : Integral a => a -> Stream a
lincong = tail . (iterate (\n => (1103515245 * n + 12345) `mod` 2147483648))

randishInts : Nat -> Integer -> List Integer
randishInts size seed = take size $ lincong seed

mylast : List a -> Maybe a
mylast [] = Nothing
mylast [x] = Just x
mylast (x::xs) = mylast xs

doSort : Nat -> IO ()
doSort Z     = putStrLn "Done"
doSort (S k) = do let xs = sort $ randishInts 12000 $ natToInteger k
                  -- get last elem to make sure compiler doesn't optimise away the sort
                  putStrLn $ show $ mylast xs
                  doSort k

main : IO ()
main = do max <- getLine
          doSort (integerToNat (cast max))

