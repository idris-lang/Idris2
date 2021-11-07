module System.File.Support

%default total

||| Shorthand for a function in the C support libary
||| (libidris2_support, idris_file.h)
|||
||| @ fn the function name to refer to in the C support library
public export
support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support, idris_file.h"

||| Wrap x in the `Right` part of an `io . Either`.
export
ok : HasIO io => (x : a) -> io (Either err a)
ok x = pure (Right x)
