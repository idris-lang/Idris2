module TestBuffer

import Data.Buffer
import System.File

put : Show a => IO a -> IO ()
put = (>>= putStrLn . show)

main : IO ()
main = do
    Just buf <- newBuffer 60
        | Nothing => pure ()

    -- TODO: setByte is deprecated, remove once no longer in libs
    setByte buf 0 1
    setBits8 buf 1 2
    setBits16 buf 2 3
    setBits32 buf 4 4
    setBits64 buf 8 5
    setInt8 buf 16 (-2)
    setInt16 buf 17 (-3)
    setInt32 buf 19 (-4)
    setInt64 buf 23 (-5)

    setInt buf 31 0x1122334455667788
    setDouble buf 39 (sqrt 2)

    let helloWorld = "Hello, world"

    Just helloWorldBuf <- newBuffer (stringByteLength helloWorld)
        | Nothing => pure ()

    setString helloWorldBuf 0 "Hello, world"
    copyData helloWorldBuf 0 12 buf 47

    put $ rawSize buf

    -- TODO: getByte is deprecated, remove once no longer in libs
    put $ getByte buf 0
    put $ getBits8 buf 1
    put $ getBits16 buf 2
    put $ getBits32 buf 4
    put $ getBits64 buf 8
    put $ getInt8 buf 16
    put $ getInt16 buf 17
    put $ getInt32 buf 19
    put $ getInt64 buf 23
    put $ getInt buf 31
    put $ getDouble buf 39
    put $ getString buf 47 12

    put $ bufferData' buf

    Just readBuf <- newBuffer 8
        | Nothing => pure ()
    Right f <- openFile "testRead.buf" Read
        | Left err => put $ pure err
    Right 8 <- readBufferData f readBuf 0 8
        | Right size => put $ pure "\{show size} bytes have been read, 8 expected"
        | Left err => put $ pure err
    put $ bufferData' readBuf

    Just writeBuf <- newBuffer 8
        | Nothing => pure ()
    setInt writeBuf 0 0x7766554433221100
    Right f <- openFile "testWrite.buf" WriteTruncate
        | Left err => put $ pure err
    Right () <- writeBufferData f writeBuf 0 8
        | Left err => put $ pure err

    pure ()
