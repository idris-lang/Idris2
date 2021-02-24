module Main

import System.Concurrency

main : IO ()
main = do
    sema <- makeSemaphore 0
    ignore $ fork $ do
        putStrLn "Hello"
        semaphorePost sema
        semaphorePost sema
    semaphoreWait sema
    semaphoreWait sema
    putStrLn "Goodbye"
