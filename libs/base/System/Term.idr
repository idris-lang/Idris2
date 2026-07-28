module System.Term

%default total

libterm : String -> String
libterm s = "C:" ++ s ++ ", libidris2_support, idris_term.h"

%foreign libterm "idris2_setupTerm"
         "node:lambda:()=>undefined"
prim__setupTerm : PrimIO ()

%foreign libterm "idris2_getTermCols"
         "node:lambda:()=>(process.stdout.columns ? BigInt(process.stdout.columns) : 0)"
prim__getTermCols : PrimIO Int

%foreign libterm "idris2_getTermLines"
         "node:lambda:()=>(process.stdout.rows ? BigInt(process.stdout.rows) : 0)"
prim__getTermLines : PrimIO Int

export
setupTerm : IO ()
setupTerm = primIO prim__setupTerm

||| Get the number of columns in the terminal associated
||| with stdout. If stdout is not a TTY terminal or for
||| some other reason the width fails to be read you will
||| get 0.
export
getTermCols : IO Int
getTermCols = primIO prim__getTermCols

||| Get the number of rows in the terminal associated
||| with stdout. If stdout is not a TTY terminal or for
||| some other reason the height fails to be read you
||| will get 0.
export
getTermLines : IO Int
getTermLines = primIO prim__getTermLines
