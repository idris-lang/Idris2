module System.File.Support

%default total

public export
support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support, idris_file.h"

export
ok : HasIO io => a -> io (Either err a)
ok x = pure (Right x)
