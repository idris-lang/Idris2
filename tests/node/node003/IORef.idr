import Data.IORef

main : IO ()
main
    = do x <- newIORef 42
         let y = x
         writeIORef y 94
         val <- readIORef x
         printLn val
         val <- readIORef y
         printLn val
         modifyIORef x (* 2)
         val <- readIORef x
         printLn val
         val <- readIORef y
         printLn val
