module Control.App.FileIO

import Control.App

import System.File

%default covering

toFileEx : FileError -> FileEx
toFileEx (GenericFileError i) = GenericFileEx i
toFileEx FileReadError = FileReadError
toFileEx FileWriteError = FileWriteError
toFileEx FileNotFound = FileNotFound
toFileEx PermissionDenied = PermissionDenied
toFileEx FileExists = FileExists

public export
interface Has [Exception IOError] e => FileIO e where
  withFile : String -> Mode ->
             (onError : IOError -> App e a) ->
             (onOpen : File -> App e a) ->
             App e a
  fGetStr : File -> App e String
  fGetChars : File -> Int -> App e String
  fGetChar : File -> App e Char
  fPutStr : File -> String -> App e ()
  fPutStrLn : File -> String -> App e ()
  fflush : File -> App e ()
  fEOF : File -> App e Bool

-- TODO : Add Binary File IO with buffers

export
readFile : FileIO e => String -> App e String
readFile f
    = withFile f Read throw $ \h =>
        do content <- read [] h
           pure (fastConcat content)
  where
    read : List String -> File -> App e (List String)
    read acc h
        = do eof <- FileIO.fEOF h
             if eof
                then pure (reverse acc)
                else do str <- fGetStr h
                        read (str :: acc) h

fileOp : IO (Either FileError a) -> Has [PrimIO, Exception IOError] e => App e a
fileOp fileRes
      = do Right res <- primIO $ fileRes
             | Left err => throw (FileErr (toFileEx err))
           pure res

export
Has [PrimIO, Exception IOError] e => FileIO e where
  withFile fname m onError proc
      = do Right h <- primIO $ openFile fname m
              | Left err => onError (FileErr (toFileEx err))
           res <- catch (proc h) onError
           primIO $ closeFile h
           pure res

  fGetStr f = fileOp (fGetLine f)

  fGetChars f n = fileOp (fGetChars f n)

  fGetChar f = fileOp (fGetChar f)

  fPutStr f str = fileOp (fPutStr f str)

  fPutStrLn f str = fileOp (File.ReadWrite.fPutStrLn f str)

  fflush f = primIO $ fflush f

  fEOF f = primIO $ fEOF f

export
withFileIO : Has [PrimIO] e =>
             App (IOError :: e) a ->
             (ok : a -> App e b) ->
             (err : IOError -> App e b) -> App e b
withFileIO prog ok err = handle prog ok err
