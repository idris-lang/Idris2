module System.File

import Data.Buffer

import public System.File.Buffer
import public System.File.Error
import public System.File.Handle
import public System.File.Meta
import public System.File.Mode
import public System.File.Permissions
import public System.File.Process
import public System.File.ReadWrite
import public System.File.Types
import public System.File.Virtual

||| Copy the file at the specified source to the given destination.
||| Returns the number of bytes that have been written upon a write error.
|||
||| @ src  the file to copy
||| @ dest the place to copy the file to
export
copyFile : HasIO io => (src : String) -> (dest : String) -> io (Either (FileError, Int) ())
copyFile src dest
    = do Right buf <- createBufferFromFile src
             | Left err => pure (Left (err, 0))
         writeBufferToFile dest buf !(rawSize buf)
