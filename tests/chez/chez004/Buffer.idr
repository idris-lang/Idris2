import Data.Buffer
import System.File

main : IO ()
main
    = do Just buf <- newBuffer 100
              | Nothing => putStrLn "Buffer creation failed"
         s <- rawSize buf
         printLn s

         setInt32 buf 1 94
         setString buf 5 "AAAA"
         val <- getInt32 buf 1
         printLn val

         setDouble buf 10 94.42
         val <- getDouble buf 10
         printLn val

         setString buf 20 "Hello there!"
         val <- getString buf 20 5
         printLn val

         val <- getString buf 26 6
         printLn val

         ds <- bufferData buf
         printLn ds

         Right _ <- writeBufferToFile "test.buf" buf 100
             | Left err => putStrLn "Buffer write fail"
         Right buf2 <- createBufferFromFile "test.buf"
             | Left err => putStrLn "Buffer read fail"

         ds <- bufferData buf2
         printLn ds

         freeBuffer buf
         freeBuffer buf2

-- Put back when the File API is moved to C and these can work again
--          Right f <- openBinaryFile "test.buf" Read
--              | Left err => putStrLn "File error on read"
--          Just buf3 <- newBuffer 99
--               | Nothing => putStrLn "Buffer creation failed"
--          Right _ <- readBufferFromFile f buf3 100
--              | Left err => do putStrLn "Buffer read fail"
--                               closeFile f
--          closeFile f

