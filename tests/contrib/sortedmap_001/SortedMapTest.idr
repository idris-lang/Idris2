import Data.SortedMap

(&~) : a -> (a -> b) -> b
(&~) x f = f x

infixl 2 &~

testLookupBetween : List (Maybe (Maybe (Int,Int),Maybe (Int,Int)))
testLookupBetween =
  let maps : List (((Maybe (Int,Int), Maybe (Int,Int))),(Maybe (Int,Int), Maybe (Int,Int)))
      maps =
        [
         (lookupBetween 1 (singleton 0 10),((Just (0,10)), Nothing))
        ,(lookupBetween 1 (singleton 0 10 &~ insert 9 90), (Just (0,10), Just (9,90)))
        ,(lookupBetween 7 (singleton 0 10 &~ insert 5 50 &~ insert 9 90 &~ delete 5), (Just (0,10), Just (9,90)))
        ,(lookupBetween (-1) (singleton 0 10), (Nothing,Just (0,10)))
        ,(lookupBetween (-1) (singleton 0 10 &~ insert 9 90), (Nothing,Just (0,10)))
        ,(lookupBetween (-1) (singleton 0 10 &~ insert 9 90 &~ insert 5 50), (Nothing,Just (0,10)))
        ,(lookupBetween (-1) (singleton 0 10 &~ insert 6 60), (Nothing,Just (0,10)))
        ,(lookupBetween 1 (singleton 0 10 &~ insert 9 90 &~ insert 5 50 &~ insert 3 30 &~ insert 7 70 &~ delete 3 &~ delete 7),
                        (Just (0,10),Just (5,50)))
        ,(lookupBetween 4 (singleton 0 10 &~ insert 9 90 &~ insert 5 50 &~ insert 3 30 &~ insert 7 70 &~ delete 3 &~ delete 7),
                        (Just (0,10),Just (5,50)))
        ,(lookupBetween 6 (singleton 0 10 &~ insert 9 90 &~ insert 5 50 &~ insert 3 30 &~ insert 7 70 &~ delete 3 &~ delete 7),
                        (Just (5,50),Just (9,90)))
        ,(lookupBetween 8 (singleton 0 10 &~ insert 9 90 &~ insert 5 50 &~ insert 3 30 &~ insert 7 70 &~ delete 3 &~ delete 7),
                        (Just (5,50),Just (9,90)))
        ,(lookupBetween 10 (singleton 0 10 &~ insert 9 90 &~ insert 5 50 &~ insert 3 30 &~ insert 7 70 &~ delete 3 &~ delete 7),
                        (Just (9,90), Nothing))
        ,(lookupBetween 100 (singleton 10 100 &~ insert 15 150 &~ insert 40 400 &~ insert 60 600 &~ insert 80 800 &~ insert 90 900),
                        (Just (90,900), Nothing))
        ,(lookupBetween 100 (singleton 10 100 &~ insert 15 150 &~ insert 40 400 &~ insert 60 600 &~ insert 80 800 &~ insert 90 900),
                        (Just (90,900), Nothing))
        ,(lookupBetween 61 (singleton 10 100 &~ insert 15 150 &~ insert 40 400 &~ insert 60 600 &~ insert 80 800 &~ insert 90 900),
                        (Just (60,600), Just (80,800)))
        ]
  in
    map (\(t,ev) => if t == ev then Nothing else Just t) maps

testLeftRight : List (Maybe (Maybe (Int,Int)))
testLeftRight =
  let maps : List (Maybe (Int,Int),Maybe (Int,Int))
      maps =
        [
         (leftMost (singleton 10 100 &~ insert 15 150 &~ insert 40 400 &~ insert 60 600 &~ insert 80 800 &~ insert 90 900), Just (10,100))
        ,(rightMost (singleton 10 100 &~ insert 15 150 &~ insert 40 400 &~ insert 60 600 &~ insert 80 800 &~ insert 90 900), Just (90,900))
        ]
  in
    map (\(t,ev) => if t == ev then Nothing else Just t) maps

main : IO ()
main =
  do
    ignore $ traverse printLn testLookupBetween
    ignore $ traverse printLn testLeftRight


