module Main

pure : Applicative f => Applicative g => a -> f (g a)
pure = Prelude.pure . Prelude.pure

(<*>) : Applicative f => Applicative g => f (g $ a -> b) -> f (g a) -> f (g b)
fgf <*> fga = Prelude.[| fgf <*> fga |]

test : List (Maybe Integer)
test = Main.[| (map Just [1,2,3]) + [Just 4, Nothing] |]

main : IO ()
main = printLn test
