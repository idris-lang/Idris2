import System.File

import Control.App
import Control.App.FileIO
import Control.App.Console

testFileReadOps : File -> Has [Console, FileIO] e => App e ()
testFileReadOps file = do
    testStr <- fGetChars file 6
    putStrLn testStr
    chr <- fGetChar file
    putStrLn (show chr)
    rest <- fGetStr file
    putStrLn rest

testFileWriteOps : File -> Has [Console, FileIO] e => App e ()
testFileWriteOps file = do
    fPutStr file "Hello "
    fPutStrLn file "Idris!"
    fPutStrLn file "Another line"

runTests : Has [Console, FileIO] e => App e ()
runTests = do
    withFile "test.txt" WriteTruncate
        (\err => putStrLn $ "Failed to open file in write mode: " ++ show err)
        (\file => testFileWriteOps file)
    withFile "test.txt" Read
        (\err => putStrLn $ "Failed to open file in read mode: " ++ show err)
        (\file => testFileReadOps file)

prog : App Init ()
prog =
    handle runTests
        (\() => putStrLn "No exceptions occurred")
        (\err: IOError =>
            putStrLn $ "Caught file error : " ++ show err)

main : IO ()
main = run prog
