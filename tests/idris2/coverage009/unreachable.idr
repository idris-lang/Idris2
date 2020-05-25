foo : Maybe Int -> Bool -> Int
foo Nothing _ = 42
foo Nothing True = 94
foo (Just x) _ = x
foo Nothing False = 42
