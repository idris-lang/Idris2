module Main


data BufferPointer : Type where

%foreign "C:getBufferSize, libidris2_support, buffer.h"
getBufferSize : Ptr BufferPointer -> PrimIO Int


%foreign "C:newBuffer, libidris2_support, buffer.h"
newBuffer : Int -> PrimIO (Ptr BufferPointer)

%foreign "C:free, libc 6"
freeAnyPtr : Ptr BufferPointer -> PrimIO ()


allocPointerAndThenReferenceItAfterGC : IO ()
allocPointerAndThenReferenceItAfterGC = do
    ptr <- primIO $ newBuffer 128
    gcptr <- onCollect ptr (primIO . freeAnyPtr)
    bufferSize <- primIO $ getBufferSize ptr
    putStrLn $ "buffer size is " ++ (show bufferSize)
    pure ()

allocPointerAndGCTwice : IO ()
allocPointerAndGCTwice = do
    ptr <- primIO $ newBuffer 128
    putStrLn "buffer allocated"
    gcptr <- onCollect ptr (primIO . freeAnyPtr)
    gcptr <- onCollect ptr (primIO . freeAnyPtr)
    putStrLn "called onCollectAny twice"
    pure ()

-- AnyPtr

%foreign "C:getBufferSize, libidris2_support, buffer.h"
getBufferSize' : AnyPtr -> PrimIO Int


%foreign "C:newBuffer, libidris2_support, buffer.h"
newBuffer' : Int -> PrimIO (AnyPtr)

%foreign "C:free, libc 6"
freeAnyPtr' : AnyPtr -> PrimIO ()


allocPointerAndThenReferenceItAfterGC' : IO ()
allocPointerAndThenReferenceItAfterGC' = do
    ptr <- primIO $ newBuffer' 128
    gcptr <- onCollectAny ptr (primIO . freeAnyPtr')
    bufferSize <- primIO $ getBufferSize' ptr
    putStrLn $ "buffer size is " ++ (show bufferSize)
    pure ()

allocPointerAndGCTwice' : IO ()
allocPointerAndGCTwice' = do
    ptr <- primIO $ newBuffer' 128
    putStrLn "buffer allocated"
    gcptr <- onCollectAny ptr (primIO . freeAnyPtr')
    gcptr <- onCollectAny ptr (primIO . freeAnyPtr')
    putStrLn "called onCollectAny twice"
    pure ()


main : IO ()
main = do
    allocPointerAndThenReferenceItAfterGC
    allocPointerAndGCTwice
    allocPointerAndThenReferenceItAfterGC'
    allocPointerAndGCTwice'
