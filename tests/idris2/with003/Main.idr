module Main

import Data.List
import Data.Vect

-- add some definition of (>>=) in another namespace
namespace Other
  public export
  (>>=) : IO a -> IO b -> IO b
  (>>=) f x = f *> x
