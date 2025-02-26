module System.Term

%default total

libterm : String -> String
libterm s = "C:" ++ s ++ ", libidris2_support, idris_term.h"

%foreign libterm "idris2_setupTerm"
         "node:lambda:()=>undefined"
prim__setupTerm : PrimIO ()

%foreign libterm "idris2_getTermCols"
         "node:lambda:()=>process.stdout.columns"
prim__getTermCols : PrimIO Int

%foreign libterm "idris2_getTermLines"
         "node:lambda:()=>process.stdout.rows"
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
