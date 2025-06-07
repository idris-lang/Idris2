pls : Int -> {_ : Int} -> Int
pls = (+)

higherOrder : (Int -> {_ : Int} -> Int) -> ()
higherOrder _ = ()

foo : ()
foo = higherOrder (+)

maybePls : Maybe Int -> Maybe Int -> Maybe Int
maybePls x y = pure {f=Maybe} pls <*> x <*> y

