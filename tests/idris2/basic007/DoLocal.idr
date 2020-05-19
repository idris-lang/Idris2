import Stuff

(>>=) : (Maybe a) -> (a -> Maybe b) -> Maybe b
(>>=) Nothing k = Nothing
(>>=) (Just x) k = k x

mthings : (foo : Maybe (Maybe Int)) -> (bar : Maybe (Maybe Int)) -> Maybe Int
mthings mx my
    = do Just x <- mx
            | Nothing => Just 0
         Just y <- my
            | Nothing => Just 1
         let z : Int -> Int
             z x = prim__add_Int x y
         Just (z (prim__add_Int x x))
