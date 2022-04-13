module Debug.Trace

import Prelude
import PrimIO

%default total

export
trace : (msg : String) -> (result : a) -> a
trace x val = unsafePerformIO (do putStrLn x; pure val)

export %inline
traceValBy : (msgF : a -> String) -> (result : a) -> a
traceValBy f v = trace (f v) v

export %inline
traceVal : Show a => a -> a
traceVal = traceValBy show
