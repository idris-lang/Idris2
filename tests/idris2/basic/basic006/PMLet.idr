import Stuff

foo : Int -> Maybe Int
foo 0 = Nothing
foo x = Just (prim__mul_Int x 2)

testLet : Int -> Int
testLet x = let y = prim__mul_Int x 2
                Just ans = foo y
                     | Nothing => 99
                z = prim__mul_Int ans 2
              in z
