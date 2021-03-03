data MyCmd : Type -> Type where
  Display : String -> MyCmd ()
  Input : MyCmd String

  Pure : ty -> MyCmd ty
  (>>=) : MyCmd a -> (a -> MyCmd b) -> MyCmd b

(>>) : MyCmd () -> MyCmd a -> MyCmd a
ma >> mb = ma >>= const mb

runMyCmd : MyCmd a -> IO a
runMyCmd (Display str) = putStrLn str
runMyCmd Input = do str <- getLine
                    pure str
runMyCmd (Pure x) = pure x
runMyCmd (c >>= f) = do res <- runMyCmd c
                        runMyCmd (f res)

myCmdTest : MyCmd ()
myCmdTest = do Display "Hello"
               x <- Input
               Display x
               Pure ()
