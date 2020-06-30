import Text.Readline

echoLoop : IO ()
echoLoop
    = do Just x <- readline "> "
              | Nothing => putStrLn "EOF"
         putStrLn ("Read: " ++ x)
         when (x /= "") $ addHistory x
         if x /= "quit"
            then echoLoop
            else putStrLn "Done"

main : IO ()
main = echoLoop
