import Data.List

-- %default total

total
foo : Maybe a -> a
foo (Just x) = x

total
bar : %World -> ()
bar %MkWorld = ()

total
qsortBad : Ord a => List a -> List a
qsortBad [] = []
qsortBad (x :: xs)
   = qsortBad (filter (< x) xs) ++ x :: qsortBad (filter (> x) xs)

total
qsort : Ord a => List a -> List a
qsort [] = []
qsort (x :: xs)
   = qsort (assert_smaller (x :: xs) (filter (< x) xs)) ++
         x :: qsort (assert_smaller (x :: xs) (filter (> x) xs))

partial
main : IO ()
main = do let x = foo Nothing
          printLn (the Int x)
