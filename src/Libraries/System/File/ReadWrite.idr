module Libraries.System.File.ReadWrite

import Data.SnocList

import System.File.Handle
import System.File.ReadWrite

%default total

||| Read all the remaining contents of a file handle
export
covering
fRead : HasIO io => (h : File) -> io (Either FileError String)
fRead h = fRead' h [<]
  where
    fRead' : HasIO io' => (h : File) -> (acc : SnocList String) -> io' (Either FileError String)
    fRead' h acc = do
      if !(fEOF h)
         then pure $ Right $ concat acc
         else do
             Right line <- fGetLine h
                | Left err => pure $ Left err
             fRead' h $ acc :< line
