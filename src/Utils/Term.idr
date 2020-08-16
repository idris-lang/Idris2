module Utils.Term

import System.FFI

%default total

libterm : String -> String
libterm s = "C:" ++ s ++ ", libidris2_support"

%foreign libterm "idris2_getTermCols"
prim__getTermCols : PrimIO Int

%foreign libterm "idris2_getTermLines"
prim__getTermLines : PrimIO Int

export
getTermCols : IO Int
getTermCols = primIO prim__getTermCols

export
getTermLines : IO Int
getTermLines = primIO prim__getTermLines
