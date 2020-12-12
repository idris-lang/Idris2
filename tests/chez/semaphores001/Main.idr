module Main

import System.Concurrency.Raw

main : IO ()
main = do
    sema <- makeSemaphore 0
    semaphorePost sema
    semaphorePost sema
    putStrLn "Hello"
    semaphoreWait sema
    semaphoreWait sema
    putStrLn "Goodbye"
