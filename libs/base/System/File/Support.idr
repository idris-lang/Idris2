module System.File.Support

%default total

||| Shorthand for referring to the C support library
|||
||| @ fn the function name to refer to in the C support library
public export
supportC : (fn : String) -> String
supportC fn = "C:\{fn}, libidris2_support, idris_file.h"

||| Shorthand for referring to the Node system support library
|||
||| @ fn the function name to refer to in the js/system_support_file.js file
public export
supportNode : (fn : String) -> String
supportNode fn = "node:support:\{fn},support_system_file"

||| Wrap x in the `Right` part of an `io . Either`.
export
ok : HasIO io => (x : a) -> io (Either err a)
ok x = pure (Right x)
