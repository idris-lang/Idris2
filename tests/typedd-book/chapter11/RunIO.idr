%default total

data RunIO : Type -> Type where
     Quit : a -> RunIO a
     Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b
     Seq : IO () -> Inf (RunIO b) -> RunIO b

(>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
(>>=) = Do

(>>) : IO () -> Inf (RunIO b) -> RunIO b
(>>) = Seq

greet : RunIO ()
greet = do putStr "Enter your name: "
           name <- getLine
           if name == ""
              then do putStrLn "Bye bye!"
                      Quit ()
              else do putStrLn ("Hello " ++ name)
                      greet

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> RunIO a -> IO (Maybe a)
run fuel (Quit val) = do pure (Just val)
run (More fuel) (Do c f) = do res <- c
                              run fuel (f res)
run (More fuel) (Seq io k) = do io; run fuel k
run Dry p = pure Nothing

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = ignore $ run forever greet
