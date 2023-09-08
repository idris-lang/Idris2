data Baz : Int -> Type where
     AddThings : (x : Int) -> (y : Int) -> Baz (x + y)

addBaz : (x : Int) -> Baz x -> Int
addBaz (x + y) (AddThings x z) = x + y
