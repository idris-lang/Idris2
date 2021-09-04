module System.File.Mode

import System.Info

%default total

public export
data Mode = Read | WriteTruncate | Append | ReadWrite | ReadWriteTruncate | ReadAppend

export
modeStr : Mode -> String
modeStr Read              = if isWindows then "rb" else "r"
modeStr WriteTruncate     = if isWindows then "wb" else "w"
modeStr Append            = if isWindows then "ab" else "a"
modeStr ReadWrite         = if isWindows then "rb+" else "r+"
modeStr ReadWriteTruncate = if isWindows then "wb+" else "w+"
modeStr ReadAppend        = if isWindows then "ab+" else "a+"
