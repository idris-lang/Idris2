import System.Info

main : IO ()
main = do Just np <- getNProcessors
            | Nothing => putStrLn "ERROR: Couldn't get number of processors!"
          putStrLn $ (show np) ++ " processors"

