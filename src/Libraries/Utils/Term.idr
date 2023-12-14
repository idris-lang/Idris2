module Libraries.Utils.Term

%default total

-- TODO: remove this file and use System.Term after 0.7.0 is released

libterm : String -> String
libterm s = "C:" ++ s ++ ", libidris2_support, idris_term.h"

%foreign libterm "idris2_setupTerm"
prim__setupTerm : PrimIO ()

%foreign libterm "idris2_getTermCols"
prim__getTermCols : PrimIO Int

%foreign libterm "idris2_getTermLines"
prim__getTermLines : PrimIO Int

export
setupTerm : IO ()
setupTerm = primIO prim__setupTerm

export
getTermCols : IO Int
getTermCols = primIO prim__getTermCols

export
getTermLines : IO Int
getTermLines = primIO prim__getTermLines
