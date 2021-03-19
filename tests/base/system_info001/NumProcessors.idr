import System.Info

main : IO ()
main = do np <- getNProcessors
          putStrLn $ (show np) ++ " processors"

