module Data.Buffer

import System.File

export
data Buffer : Type where [external]

%foreign  "scheme:blodwen-buffer-size"
prim__bufferSize : Buffer -> Int

export
rawSize : Buffer -> IO Int
rawSize buf = pure (prim__bufferSize buf)

%foreign "scheme:blodwen-new-buffer"
prim__newBuffer : Int -> PrimIO Buffer

export
newBuffer : Int -> IO (Maybe Buffer)
newBuffer size
    = do buf <- primIO (prim__newBuffer size)
         pure $ Just buf
--          if prim__nullAnyPtr buf /= 0
--             then pure Nothing
--             else pure $ Just $ MkBuffer buf size 0

-- might be needed if we do this in C...
export
freeBuffer : Buffer -> IO ()
freeBuffer buf = pure ()

%foreign "scheme:blodwen-buffer-setbyte"
prim__setByte : Buffer -> Int -> Int -> PrimIO ()

-- Assumes val is in the range 0-255
export
setByte : Buffer -> (loc : Int) -> (val : Int) -> IO ()
setByte buf loc val
    = primIO (prim__setByte buf loc val)

%foreign "scheme:blodwen-buffer-getbyte"
prim__getByte : Buffer -> Int -> PrimIO Int

export
getByte : Buffer -> (loc : Int) -> IO Int
getByte buf loc
    = primIO (prim__getByte buf loc)

%foreign "scheme:blodwen-buffer-setint32"
prim__setInt32 : Buffer -> Int -> Int -> PrimIO ()

export
setInt32 : Buffer -> (loc : Int) -> (val : Int) -> IO ()
setInt32 buf loc val
    = primIO (prim__setInt32 buf loc val)

%foreign "scheme:blodwen-buffer-getint32"
prim__getInt32 : Buffer -> Int -> PrimIO Int

export
getInt32 : Buffer -> (loc : Int) -> IO Int
getInt32 buf loc
    = primIO (prim__getInt32 buf loc)

%foreign "scheme:blodwen-buffer-setint"
prim__setInt : Buffer -> Int -> Int -> PrimIO ()

export
setInt : Buffer -> (loc : Int) -> (val : Int) -> IO ()
setInt buf loc val
    = primIO (prim__setInt buf loc val)

%foreign "scheme:blodwen-buffer-getint"
prim__getInt : Buffer -> Int -> PrimIO Int

export
getInt : Buffer -> (loc : Int) -> IO Int
getInt buf loc
    = primIO (prim__getInt buf loc)

%foreign "scheme:blodwen-buffer-setdouble"
prim__setDouble : Buffer -> Int -> Double -> PrimIO ()

export
setDouble : Buffer -> (loc : Int) -> (val : Double) -> IO ()
setDouble buf loc val
    = primIO (prim__setDouble buf loc val)

%foreign "scheme:blodwen-buffer-getdouble"
prim__getDouble : Buffer -> Int -> PrimIO Double

export
getDouble : Buffer -> (loc : Int) -> IO Double
getDouble buf loc
    = primIO (prim__getDouble buf loc)

-- Get the length of a string in bytes, rather than characters
export
%foreign "C:strlen,libc 6"
stringByteLength : String -> Int

%foreign "scheme:blodwen-buffer-setstring"
prim__setString : Buffer -> Int -> String -> PrimIO ()

export
setString : Buffer -> (loc : Int) -> (val : String) -> IO ()
setString buf loc val
    = primIO (prim__setString buf loc val)

%foreign "scheme:blodwen-buffer-getstring"
prim__getString : Buffer -> Int -> Int -> PrimIO String

export
getString : Buffer -> (loc : Int) -> (len : Int) -> IO String
getString buf loc len
    = primIO (prim__getString buf loc len)

export
bufferData : Buffer -> IO (List Int)
bufferData buf
    = do len <- rawSize buf
         unpackTo [] len
  where
    unpackTo : List Int -> Int -> IO (List Int)
    unpackTo acc 0 = pure acc
    unpackTo acc loc
        = do val <- getByte buf (loc - 1)
             unpackTo (val :: acc) (loc - 1)

%foreign "scheme:blodwen-buffer-copydata"
prim__copyData : Buffer -> Int -> Int -> Buffer -> Int -> PrimIO ()

export
copyData : (src : Buffer) -> (start, len : Int) ->
           (dest : Buffer) -> (loc : Int) -> IO ()
copyData src start len dest loc
    = primIO (prim__copyData src start len dest loc)

-- %foreign "scheme:blodwen-readbuffer-bytes"
-- prim__readBufferBytes : FilePtr -> AnyPtr -> Int -> Int -> PrimIO Int
--
-- export
-- readBufferFromFile : BinaryFile -> Buffer -> (maxbytes : Int) ->
--                      IO (Either FileError Buffer)
-- readBufferFromFile (FHandle h) (MkBuffer buf size loc) max
--     = do read <- primIO (prim__readBufferBytes h buf loc max)
--          if read >= 0
--             then pure (Right (MkBuffer buf size (loc + read)))
--             else pure (Left FileReadError)

%foreign "scheme:blodwen-read-bytevec"
prim__readBufferFromFile : String -> PrimIO Buffer

%foreign "scheme:blodwen-isbytevec"
prim__isBuffer : Buffer -> Int

-- Create a new buffer by reading all the contents from the given file
-- Fails if no bytes can be read or buffer can't be created
export
createBufferFromFile : String -> IO (Either FileError Buffer)
createBufferFromFile fn
    = do buf <- primIO (prim__readBufferFromFile fn)
         if prim__isBuffer buf /= 0
            then pure (Left FileReadError)
            else do let sz = prim__bufferSize buf
                    pure (Right buf)

%foreign "scheme:blodwen-write-bytevec"
prim__writeBuffer : String -> Buffer -> Int -> PrimIO Int

export
writeBufferToFile : String -> Buffer -> (maxbytes : Int) ->
                    IO (Either FileError ())
writeBufferToFile fn buf max
    = do res <- primIO (prim__writeBuffer fn buf max)
         if res /= 0
            then pure (Left FileWriteError)
            else pure (Right ())

export
resizeBuffer : Buffer -> Int -> IO (Maybe Buffer)
resizeBuffer old newsize
    = do Just buf <- newBuffer newsize
              | Nothing => pure Nothing
         -- If the new buffer is smaller than the old one, just copy what
         -- fits
         oldsize <- rawSize old
         let len = if newsize < oldsize then newsize else oldsize
         copyData old 0 len buf 0
         freeBuffer old
         pure (Just buf)
