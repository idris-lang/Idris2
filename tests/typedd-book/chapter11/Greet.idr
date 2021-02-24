%default total

data InfIO : Type where
     Do : IO a -> (a -> Inf InfIO) -> InfIO
     Seq : IO () -> Inf InfIO -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

(>>) : IO () -> Inf InfIO -> InfIO
(>>) = Seq

greet : InfIO
greet = do putStr "Enter your name: "
           name <- getLine
           putStrLn ("Hello " ++ name)
           greet
