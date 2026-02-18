module Test

import Data.IOArray
import Data.IORef
import System.Info

main : IO ()
main = do
  do
    arr <- newArray {elem=Int} 10
    printLn !(readArray arr 0)
    printLn !(writeArray arr 1 10)
    printLn !(readArray arr 1)
  do
    ref <- newIORef "abcd"
    printLn !(readIORef ref)
    writeIORef ref "ABCD"
    printLn !(readIORef ref)
  do
    -- printLn os
    printLn codegen
