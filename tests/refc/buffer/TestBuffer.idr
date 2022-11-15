module TestBuffer

import Data.Buffer
import System.File

put : Show a => IO a -> IO ()
put = (>>= putStrLn . show)

main : IO ()
main = do
    Just buf <- newBuffer 31
        | Nothing => pure ()

    -- TODO: setByte is deprecated, remove once no longer in libs
    setByte buf 0 1
    setBits8 buf 1 2
    setInt buf 2 0x1122334455667788
    setDouble buf 10 (sqrt 2)

    let helloWorld = "Hello, world"

    Just helloWorldBuf <- newBuffer (stringByteLength helloWorld)
        | Nothing => pure ()

    setString helloWorldBuf 0 "Hello, world"
    copyData helloWorldBuf 0 12 buf 18

    put $ rawSize buf

    -- TODO: getByte is deprecated, remove once no longer in libs
    put $ getByte buf 0
    put $ getBits8 buf 1
    put $ getInt buf 2
    put $ getDouble buf 10
    put $ getString buf 18 12

    put $ bufferData buf

    Just readBuf <- newBuffer 8
        | Nothing => pure ()
    Right f <- openFile "testRead.buf" Read
        | Left err => put $ pure err
    Right 8 <- readBufferData f readBuf 0 8
        | Right size => put $ pure "\{show size} bytes have been read, 8 expected"
        | Left err => put $ pure err
    put $ bufferData readBuf

    Just writeBuf <- newBuffer 8
        | Nothing => pure ()
    setInt writeBuf 0 0x7766554433221100
    Right f <- openFile "testWrite.buf" WriteTruncate
        | Left err => put $ pure err
    Right () <- writeBufferData f writeBuf 0 8
        | Left err => put $ pure err

    pure ()
