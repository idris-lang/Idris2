test : (xs : List Int) ->  2 = length xs -> (Int, Int)
test (x1 :: x2 :: x3 :: []) pf = (x1, x2)
