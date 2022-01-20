module Libraries.Utils.Binary

import Data.Buffer
import Data.List

import Libraries.System.File

-- Serialising data as binary. Provides an interface TTC which allows
-- reading and writing to chunks of memory, "Binary", which can be written
-- to and read from files.

%default covering

public export
record Binary where
  constructor MkBin
  buf : Buffer
  loc : Int
  size : Int -- Capacity
  used : Int -- Amount used

export
newBinary : Buffer -> Int -> Binary
newBinary b s = MkBin b 0 s 0

export
blockSize : Int
blockSize = 655360

export
avail : Binary -> Int
avail c = (size c - loc c) - 1

export
toRead : Binary -> Int
toRead c = used c - loc c

export
appended : Int -> Binary -> Binary
appended i (MkBin b loc s used) = MkBin b (loc+i) s (used + i)

export
incLoc : Int -> Binary -> Binary
incLoc i c = { loc $= (+i) } c

export
dumpBin : Binary -> IO ()
dumpBin chunk
   = do -- printLn !(traverse bufferData (map buf done))
        printLn !(bufferData (buf chunk))
        -- printLn !(traverse bufferData (map buf rest))

export
nonEmptyRev : {xs : _} ->
              NonEmpty (xs ++ y :: ys)
nonEmptyRev {xs = []} = IsNonEmpty
nonEmptyRev {xs = (x :: xs)} = IsNonEmpty

export
fromBuffer : Buffer -> IO Binary
fromBuffer buf
    = do len <- rawSize buf
         pure (MkBin buf 0 len len)

export
writeToFile : (fname : String) -> Binary -> IO (Either FileError ())
writeToFile fname c
    = do Right ok <- writeBufferToFile fname (buf c) (used c)
               | Left (err, size) => pure (Left err)
         pure (Right ok)

export
readFromFile : (fname : String) -> IO (Either FileError Binary)
readFromFile fname
    = do Right b <- createBufferFromFile fname
               | Left err => pure (Left err)
         bsize <- rawSize b
         pure (Right (MkBin b 0 bsize bsize))
