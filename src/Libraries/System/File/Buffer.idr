module Libraries.System.File.Buffer

import public System.File.Error
import System.File.Handle
import System.File.Meta
import System.File.Mode
import System.File.ReadWrite
import System.File.Support
import public System.File.Types

import Data.Buffer

%default total

%foreign support "idris2_readBufferData"
         "node:lambda:(f,b,l,m) => require('fs').readSync(f.fd,b,l,m)"
prim__readBufferData : FilePtr -> Buffer -> (offset : Int) -> (maxbytes : Int) -> PrimIO Int

%foreign support "idris2_writeBufferData"
         "node:lambda:(f,b,l,m) => require('fs').writeSync(f.fd,b,l,m)"
prim__writeBufferData : FilePtr -> Buffer -> (offset : Int) -> (size : Int) -> PrimIO Int

||| Read the data from the file into the given buffer.
|||
||| @ fh       the file handle to read from
||| @ buf      the buffer to read the data into
||| @ offset   the position in buffer to start adding
||| @ maxbytes the maximum size to read; must not exceed buffer length
export
readBufferData : HasIO io => (fh : File) -> (buf : Buffer) ->
                 (offset : Int) ->
                 (maxbytes : Int) ->
                 io (Either FileError ())
readBufferData (FHandle h) buf offset max
    = do read <- primIO (prim__readBufferData h buf offset max)
         if read >= 0
            then pure (Right ())
            else pure (Left FileReadError)

||| Write the data from the buffer to the given `File`. Returns the number
||| of bytes that have been written upon a write error. Otherwise, it can
||| be assumed that `size` number of bytes have been written.
||| (If you do not have a `File` and just want to write to a file at a known
||| path, you probably want to use `writeBufferToFile`.)
|||
||| @ fh       the file handle to write to
||| @ buf      the buffer from which to get the data to write
||| @ offset   the position in buffer to write from
||| @ size     the number of bytes to write; must not exceed buffer length
export
writeBufferData : HasIO io => (fh : File) -> (buf : Buffer) ->
                  (offset : Int) ->
                  (size : Int) ->
                  io (Either (FileError, Int) ())
writeBufferData (FHandle h) buf offset size
    = do written <- primIO (prim__writeBufferData h buf offset size)
         if written == size
            then pure (Right ())
            else pure (Left (FileWriteError, written))

||| Attempt to write the data from the buffer to the file at the specified file
||| name. Returns the number of bytes that have been written upon a write error.
||| Otherwise, it can be assumed that `size` number of bytes have been written.
|||
||| @ fn   the file name to write to
||| @ buf  the buffer from which to get the data to write
||| @ size the number of bytes to write; must not exceed buffer length
export
writeBufferToFile : HasIO io => (fn : String) -> (buf : Buffer) -> (size : Int) ->
                                io (Either (FileError, Int) ())
writeBufferToFile fn buf size
    = do Right f <- openFile fn WriteTruncate
             | Left err => pure (Left (err, 0))
         Right ok <- writeBufferData f buf 0 size
             | Left err => pure (Left err)
         closeFile f
         pure (Right ok)

||| Create a new buffer by opening a file and reading its contents into a new
||| buffer whose size matches the file size.
|||
||| @ fn the name of the file to read
export
createBufferFromFile : HasIO io => (fn : String) -> io (Either FileError Buffer)
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
