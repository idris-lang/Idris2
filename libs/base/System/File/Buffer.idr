module System.File.Buffer

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
prim__writeBufferData : FilePtr -> Buffer -> (offset : Int) -> (maxbytes : Int) -> PrimIO Int

export
readBufferData : HasIO io => File -> Buffer ->
                 (offset : Int) -> -- position in buffer to start adding
                 (maxbytes : Int) -> -- maximums size to read, which must not
                                     -- exceed buffer length
                 io (Either FileError ())
readBufferData (FHandle h) buf offset max
    = do read <- primIO (prim__readBufferData h buf offset max)
         if read >= 0
            then pure (Right ())
            else pure (Left FileReadError)

export
writeBufferData : HasIO io => File -> Buffer ->
                  (offset : Int) -> -- position in buffer to write from
                  (maxbytes : Int) -> -- maximums size to write, which must not
                                      -- exceed buffer length
                  io (Either FileError ())
writeBufferData (FHandle h) buf offset max
    = do written <- primIO (prim__writeBufferData h buf offset max)
         if written >= 0
            then pure (Right ())
            else pure (Left FileWriteError)

export
writeBufferToFile : HasIO io => String -> Buffer -> Int -> io (Either FileError ())
writeBufferToFile fn buf max
    = do Right f <- openFile fn WriteTruncate
             | Left err => pure (Left err)
         Right ok <- writeBufferData f buf 0 max
             | Left err => pure (Left err)
         closeFile f
         pure (Right ok)

export
createBufferFromFile : HasIO io => String -> io (Either FileError Buffer)
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
