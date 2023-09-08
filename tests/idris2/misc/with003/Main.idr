module Main

import Data.List
import Data.Vect

-- needs to be concretely in IO to test error messages
myPrintLn : String -> IO ()
myPrintLn = printLn

-- add some definition of (>>=) in another namespace
namespace Other
  public export
  (>>) : IO () -> IO b -> IO b
  (>>) f x = f *> x
