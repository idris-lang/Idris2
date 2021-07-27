module System.File.ReadWrite

import public Data.Fuel

import Data.List

import System.File.Handle
import public System.File.Error
import System.File.Support
import public System.File.Types

%default total

%foreign support "idris2_seekLine"
         "node:support:seekLine,support_system_file"
prim__seekLine : FilePtr -> PrimIO Int

%foreign support "idris2_readLine"
         "node:support:readLine,support_system_file"
prim__readLine : FilePtr -> PrimIO (Ptr String)

%foreign support "idris2_readChars"
prim__readChars : Int -> FilePtr -> PrimIO (Ptr String)
%foreign "C:fgetc,libc 6"
prim__readChar : FilePtr -> PrimIO Int

%foreign support "idris2_writeLine"
         "node:lambda:(filePtr, line) => require('fs').writeSync(filePtr.fd, line, undefined, 'utf-8')"
prim__writeLine : FilePtr -> String -> PrimIO Int

%foreign support "idris2_eof"
         "node:lambda:x=>(x.eof?1:0)"
prim__eof : FilePtr -> PrimIO Int

%foreign support "idris2_removeFile"
prim__removeFile : String -> PrimIO Int

||| Seek through the next newline.
||| This is @fGetLine@ without the overhead of copying
||| any characters.
export
fSeekLine : HasIO io => (h : File) -> io (Either FileError ())
fSeekLine (FHandle f)
    = do res <- primIO (prim__seekLine f)
         if res /= 0
            then returnError
            else ok ()

export
fGetLine : HasIO io => (h : File) -> io (Either FileError String)
fGetLine (FHandle f)
    = do res <- primIO (prim__readLine f)
         if prim__nullPtr res /= 0
            then returnError
            else ok (prim__getString res)

export
fGetChars : HasIO io => (h : File) -> Int -> io (Either FileError String)
fGetChars (FHandle f) max
    = do res <- primIO (prim__readChars max f)
         if prim__nullPtr res /= 0
            then returnError
            else ok (prim__getString res)

export
fGetChar : HasIO io => (h : File) -> io (Either FileError Char)
fGetChar h@(FHandle f)
    = do c <- primIO (prim__readChar f)
         ferr <- fileError h
         if ferr
            then returnError
            else ok (cast c)

export
fPutStr : HasIO io => (h : File) -> String -> io (Either FileError ())
fPutStr (FHandle f) str
    = do res <- primIO (prim__writeLine f str)
         if res == 0
            then returnError
            else ok ()

export
fPutStrLn : HasIO io => (h : File) -> String -> io (Either FileError ())
fPutStrLn f str = fPutStr f (str ++ "\n")

export
fEOF : HasIO io => (h : File) -> io Bool
fEOF (FHandle f)
    = do res <- primIO (prim__eof f)
         pure (res /= 0)

export
removeFile : HasIO io => String -> io (Either FileError ())
removeFile fname
    = do res <- primIO (prim__removeFile fname)
         if res == 0
            then ok ()
            else returnError

readLinesOnto : HasIO io => (acc : List String) ->
                            (offset : Nat) ->
                            (fuel : Fuel) ->
                            File ->
                            io (Either FileError (Bool, List String))
readLinesOnto acc _ Dry h = pure (Right (False, reverse acc))
readLinesOnto acc offset (More fuel) h
  = do False <- fEOF h
         | True => pure $ Right (True, reverse acc)
       case offset of
            (S offset') => (fSeekLine h *> readLinesOnto acc offset' (More fuel) h) @{Applicative.Compose}
            0           => (fGetLine h >>= \str => readLinesOnto (str :: acc) 0 fuel h) @{Monad.Compose}

||| Read a chunk of a file in a line-delimited fashion.
||| You can use this function to read an entire file
||| as with @readFile@ by reading until @forever@ or by
||| iterating through pages until hitting the end of
||| the file.
|||
||| The @limit@ function can provide you with enough
||| fuel to read exactly a given number of lines.
|||
||| On success, returns a tuple of whether the end of
||| the file was reached or not and the lines read in
||| from the file.
|||
||| Note that each line will still have a newline
||| character at the end.
|||
||| Important: because we are chunking by lines, this
||| function's totality depends on the assumption that
||| no single line in the input file is infinite.
export
readFilePage : HasIO io => (offset : Nat) -> (until : Fuel) -> String -> io (Either FileError (Bool, List String))
readFilePage offset fuel file
  = withFile file Read pure $
      readLinesOnto [] offset fuel

export
partial
readFile : HasIO io => String -> io (Either FileError String)
readFile = (map $ map (fastConcat . snd)) . readFilePage 0 forever

||| Write a string to a file
export
writeFile : HasIO io =>
            (filepath : String) -> (contents : String) ->
            io (Either FileError ())
writeFile file contents
  = withFile file WriteTruncate pure $
      (flip fPutStr contents)
