module MainConflict

import NonConflict1
import NonConflict2

exec : IO ()
exec = printLn (10 &&& 10 &&& 1)
