module Data.Buffer

import System.Directory
import System.File

-- Reading and writing binary buffers. Note that this primitives are unsafe,
-- in that they don't check that buffer locations are within bounds.
-- We really need a safe wrapper!
-- They are used in the Idris compiler itself for reading/writing checked
-- files.

-- This is known to the compiler, so maybe ought to be moved to Builtin
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
%foreign "scheme:blodwen-buffer-setbyte"
prim__setBits8 : Buffer -> Int -> Bits8 -> PrimIO ()

-- Assumes val is in the range 0-255
export
setByte : Buffer -> (loc : Int) -> (val : Int) -> IO ()
setByte buf loc val
    = primIO (prim__setByte buf loc val)

export
setBits8 : Buffer -> (loc : Int) -> (val : Bits8) -> IO ()
setBits8 buf loc val
    = primIO (prim__setBits8 buf loc val)

%foreign "scheme:blodwen-buffer-getbyte"
prim__getByte : Buffer -> Int -> PrimIO Int
%foreign "scheme:blodwen-buffer-getbyte"
prim__getBits8 : Buffer -> Int -> PrimIO Bits8

export
getByte : Buffer -> (loc : Int) -> IO Int
getByte buf loc
    = primIO (prim__getByte buf loc)

export
getBits8 : Buffer -> (loc : Int) -> IO Bits8
getBits8 buf loc
    = primIO (prim__getBits8 buf loc)

%foreign "scheme:blodwen-buffer-setbits16"
prim__setBits16 : Buffer -> Int -> Bits16 -> PrimIO ()

export
setBits16 : Buffer -> (loc : Int) -> (val : Bits16) -> IO ()
setBits16 buf loc val
    = primIO (prim__setBits16 buf loc val)

%foreign "scheme:blodwen-buffer-getbits16"
prim__getBits16 : Buffer -> Int -> PrimIO Bits16

export
getBits16 : Buffer -> (loc : Int) -> IO Bits16
getBits16 buf loc
    = primIO (prim__getBits16 buf loc)

%foreign "scheme:blodwen-buffer-setbits32"
prim__setBits32 : Buffer -> Int -> Bits32 -> PrimIO ()

export
setBits32 : Buffer -> (loc : Int) -> (val : Bits32) -> IO ()
setBits32 buf loc val
    = primIO (prim__setBits32 buf loc val)

%foreign "scheme:blodwen-buffer-getbits32"
prim__getBits32 : Buffer -> Int -> PrimIO Bits32

export
getBits32 : Buffer -> (loc : Int) -> IO Bits32
getBits32 buf loc
    = primIO (prim__getBits32 buf loc)

%foreign "scheme:blodwen-buffer-setbits64"
prim__setBits64 : Buffer -> Int -> Bits64 -> PrimIO ()

export
setBits64 : Buffer -> (loc : Int) -> (val : Bits64) -> IO ()
setBits64 buf loc val
    = primIO (prim__setBits64 buf loc val)

%foreign "scheme:blodwen-buffer-getbits64"
prim__getBits64 : Buffer -> Int -> PrimIO Bits64

export
getBits64 : Buffer -> (loc : Int) -> IO Bits64
getBits64 buf loc
    = primIO (prim__getBits64 buf loc)

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

%foreign "C:idris2_readBufferData,libidris2_support"
prim__readBufferData : FilePtr -> Buffer -> Int -> Int -> PrimIO Int
%foreign "C:idris2_writeBufferData,libidris2_support"
prim__writeBufferData : FilePtr -> Buffer -> Int -> Int -> PrimIO Int

export
readBufferData : File -> Buffer ->
                 (loc : Int) -> -- position in buffer to start adding
                 (maxbytes : Int) -> -- maximums size to read, which must not
                                     -- exceed buffer length
                 IO (Either FileError ())
readBufferData (FHandle h) buf loc max
    = do read <- primIO (prim__readBufferData h buf loc max)
         if read >= 0
            then pure (Right ())
            else pure (Left FileReadError)

export
writeBufferData : File -> Buffer ->
                  (loc : Int) -> -- position in buffer to write from
                  (maxbytes : Int) -> -- maximums size to write, which must not
                                      -- exceed buffer length
                  IO (Either FileError ())
writeBufferData (FHandle h) buf loc max
    = do written <- primIO (prim__writeBufferData h buf loc max)
         if written >= 0
            then pure (Right ())
            else pure (Left FileWriteError)

export
writeBufferToFile : String -> Buffer -> Int -> IO (Either FileError ())
writeBufferToFile fn buf max
    = do Right f <- openFile fn WriteTruncate
             | Left err => pure (Left err)
         Right ok <- writeBufferData f buf 0 max
             | Left err => pure (Left err)
         closeFile f
         pure (Right ok)

export
createBufferFromFile : String -> IO (Either FileError Buffer)
createBufferFromFile fn
    = do Right f <- openFile fn Read
             | Left err => pure (Left err)
         Right size <- fileSize f
             | Left err => pure (Left err)
         Just buf <- newBuffer size
             | Nothing => pure (Left FileReadError)
         Right ok <- readBufferData f buf 0 size
             | Left err => pure (Left err)
         closeFile f
         pure (Right buf)

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
