module Debug.Trace

import Prelude
import PrimIO

%default total

export
trace : (msg : String) -> (result : a) -> a
trace x val = unsafePerformIO (do putStrLn x; pure val)
