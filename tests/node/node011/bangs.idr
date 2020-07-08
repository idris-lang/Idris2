
add : Int -> Int -> Int
add = (+)

-- lift to nearest binder
addm1 : Maybe Int -> Maybe Int -> Maybe Int
addm1 x y = let z = x in pure (add !z !y)

-- lift to nearest binder
addm2 : Maybe Int -> Maybe Int -> Maybe Int
addm2 = \x, y => pure (!x + !y)

getLen : String -> IO Nat
getLen str = pure (length str)

fakeGetLine : String -> IO String
fakeGetLine str = pure str

-- lift out innermost first
printThing1 : IO ()
printThing1 = printLn !(getLen !(fakeGetLine "line1"))

-- lift out leftmost first
printThing2 : IO ()
printThing2 = printLn (!(fakeGetLine "1") ++ !(fakeGetLine "2"))

-- don't lift out of if
printBool : Bool -> IO ()
printBool x
    = if x
         then putStrLn !(fakeGetLine "True")
         else putStrLn !(fakeGetLine "False")
