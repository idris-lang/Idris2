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

export
copyFile : HasIO io => String -> String -> io (Either FileError ())
copyFile src dest
    = do Right buf <- createBufferFromFile src
             | Left err => pure (Left err)
         writeBufferToFile dest buf !(rawSize buf)
