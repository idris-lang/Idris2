||| Miscellaneous functions for getting information about the system.
module System.Info

%default total

%extern prim__os : String
%extern prim__codegen : String

||| The current operating system.
export
os : String
os = prim__os

||| The codegen/backend used.
export
codegen : String
codegen = prim__codegen

||| Whether we are running on MS Windows, either directly or with a compability
||| layer (e.g. cygwin).
export
isWindows : Bool
isWindows = os `elem` ["windows", "mingw32", "cygwin32"]

%foreign "C:idris2_getNProcessors, libidris2_support, idris_support.h"
         "node:lambda:() => require('os').cpus().length"
prim__getNProcessors : PrimIO Int

||| Get the number of processors on the system. Returns `Nothing` if we somehow
||| got 0 processors.
export
getNProcessors : IO (Maybe Nat)
getNProcessors = do
  i <- fromPrim prim__getNProcessors
  pure (if i < 0 then Nothing else Just (integerToNat (cast i)))
