module Libraries.Utils.Binary

import Data.Buffer
import Data.List

import System.File

-- Serialising data as binary. Provides an interface TTC which allows
-- reading and writing to chunks of memory, "Binary", which can be written
-- to and read from files.

%default covering

public export
record Binary where
  constructor MkBin
  buf : Buffer
  loc : Integer
  size : Integer -- Capacity
  used : Integer -- Amount used

export
newBinary : Buffer -> Integer -> Binary
newBinary b s = MkBin b 0 s 0

%inline export
blockSize : Int
blockSize = 655360

export
avail : Binary -> Integer
avail c = (size c - loc c) - 1

export
toRead : Binary -> Integer
toRead c = used c - loc c

export
appended : Integer -> Binary -> Binary
appended i (MkBin b loc s used) = MkBin b (loc+i) s (used + i)

export
incLoc : Integer -> Binary -> Binary
incLoc i c = { loc $= (+i) } c

-- TODO: remove this function once Idris2 v0.8.0 has been released
--       and use the version from base instead.
covering
bufferData' : HasIO io => Buffer -> io (List Bits8)
bufferData' buf
    = do len <- rawSize buf
         unpackTo [] len
  where
    covering
    unpackTo : List Bits8 -> Int -> io (List Bits8)
    unpackTo acc 0 = pure acc
    unpackTo acc offset
        = do val <- getBits8 buf (offset - 1)
             unpackTo (val :: acc) (offset - 1)

export
dumpBin : Binary -> IO ()
dumpBin chunk
   = do -- printLn !(traverse Binary.bufferData' (map buf done))
        printLn !(Binary.bufferData' (buf chunk))
        -- printLn !(traverse Binary.bufferData' (map buf rest))

export
nonEmptyRev : {xs : _} ->
              NonEmpty (xs ++ y :: ys)
nonEmptyRev {xs = []} = IsNonEmpty
nonEmptyRev {xs = (x :: xs)} = IsNonEmpty

export
fromBuffer : Buffer -> IO Binary
fromBuffer buf
    = do len <- rawSize buf
         let len = cast len
         pure (MkBin buf 0 len len)

export
writeToFile : (fname : String) -> Binary -> IO (Either FileError ())
writeToFile fname c
    = do Right ok <- writeBufferToFile fname (buf c) (cast $ used c)
               | Left (err, size) => pure (Left err)
         pure (Right ok)

export
readFromFile : (fname : String) -> IO (Either FileError Binary)
readFromFile fname
    = do Right b <- createBufferFromFile fname
               | Left err => pure (Left err)
         bsize <- rawSize b
         let bsize = cast bsize
         pure (Right (MkBin b 0 bsize bsize))
