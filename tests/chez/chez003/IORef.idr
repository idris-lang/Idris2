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
         z   <- newIORef 42
         val <- readIORef z
         printLn val
         t1 <- fork $ do
           atomicModifyIORef z (* 2)
         t2 <- fork $
           atomicModifyIORef z (* 2)
         threadWait t1
         threadWait t2
         val <- readIORef z
         printLn val
