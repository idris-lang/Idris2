module Control.App.FileIO

import Control.App

import Data.List
import Data.Strings
import System.File

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
  fEOF : File -> App e Bool

-- TODO : Add Binary File IO with buffers

export
readFile : FileIO e => String -> App e String
readFile f
    = withFile f Read throw $ \h =>
        do content <- read [] h
           pure (fastAppend content)
  where
    read : List String -> File -> App e (List String)
    read acc h
        = do eof <- FileIO.fEOF h
             if eof
                then pure (reverse acc)
                else do str <- fGetStr h
                        read (str :: acc) h

export
Has [PrimIO, Exception IOError] e => FileIO e where
  withFile fname m onError proc
      = do Right h <- primIO $ openFile fname m
              | Left err => onError (FileErr (toFileEx err))
           res <- catch (proc h) onError
           primIO $ closeFile h
           pure res

  fGetStr f
      = do Right str <- primIO $ fGetLine f
              | Left err => throw (FileErr (toFileEx err))
           pure str

  fGetChars f n
       = do Right str <- primIO $ fGetChars f n
              | Left err => throw (FileErr (toFileEx err))
            pure str

  fGetChar f
       = do Right chr <- primIO $ fGetChar f
              | Left err => throw (FileErr (toFileEx err))
            pure chr

  fPutStr f str
      = do Right () <- primIO $ File.fPutStr f str
               | Left err => throw (FileErr (toFileEx err))
           pure ()

  fPutStrLn f str
      = do Right () <- primIO $ File.fPutStrLn f str
               | Left err => throw (FileErr (toFileEx err))
           pure ()

  fEOF f = primIO $ fEOF f

export
withFileIO : Has [PrimIO] e =>
             App (IOError :: e) a ->
             (ok : a -> App e b) ->
             (err : IOError -> App e b) -> App e b
withFileIO prog ok err = handle prog ok err
