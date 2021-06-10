module TestBuffer

import Data.Buffer
import System.File

put : Show a => IO a -> IO ()
put = (>>= putStrLn . show)

main : IO ()
main = do
    Just buf <- newBuffer 23
        | Nothing => pure ()

    setByte buf 0 1
    setBits8 buf 1 2
    setDouble buf 2 (sqrt 2)

    let helloWorld = "Hello, world"

    Just helloWorldBuf <- newBuffer (stringByteLength helloWorld)
        | Nothing => pure ()

    setString helloWorldBuf 0 "Hello, world"
    copyData helloWorldBuf 0 12 buf 10

    put $ rawSize buf

    put $ getByte buf 0
    put $ getBits8 buf 1
    put $ getDouble buf 2
    put $ getString buf 10 12

    put $ bufferData buf

    Just readBuf <- newBuffer 8
        | Nothing => pure ()
    Right f <- openFile "testRead.buf" Read
        | Left err => put $ pure err
    Right () <- readBufferData f readBuf 0 8
        | Left err => put $ pure err
    put $ bufferData readBuf

    Just writeBuf <- newBuffer 8
        | Nothing => pure ()
    setInt writeBuf 0 0x7766554433221100
    Right f <- openFile "testWrite.buf" WriteTruncate
        | Left err => put $ pure err
    Right () <- writeBufferData f writeBuf 0 8
        | Left err => put $ pure err

    freeBuffer helloWorldBuf
    freeBuffer buf
