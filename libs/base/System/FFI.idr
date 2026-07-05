||| Additional FFI help for more interesting C types
module System.FFI
-- Some assumptions are made about the existence of this module in
-- Compiler.CompileExpr

import public Data.String -- using `words`

%default total

||| A struct with a name and a list of key-value pairs of field names and their
||| types.
export
data Struct : String -> -- C struct name
              List (String, Type) -> -- field names and types
              Type where

||| A proof that the field exists as an entry in the list of field names and
||| their types.
public export
data FieldType : List String -> Type -> List (String, Type) -> Type where
  StructField :
    FieldType ns t fields ->
    FieldType (n :: ns) t ((n, Struct name fields) :: ts)
  StructFieldPtr :
    FieldType ns t fields ->
    FieldType (n :: "*" :: ns) t ((n, Ptr (Struct name fields)) :: ts)
  UnionCase :
    FieldType ns t cases ->
    FieldType (n :: ns) t ((n, Union name cases) :: ts)
  UnionFieldPtr :
    FieldType ns t fields ->
    FieldType (n :: "*" :: ns) t ((n, Ptr (Union name fields)) :: ts)
  Here : FieldType (n :: []) t ((n, t) :: ts)
  There : FieldType ns t ts -> FieldType ns t (f :: ts)

%extern
prim__getField : {s : _} -> forall fs, ty .
                         Ptr (Struct s fs) -> (n : String) ->
                         FieldType (words n) ty fs -> ty
%extern
prim__getFieldPtr : {s : _} -> forall fs, ty .
                         Ptr (Struct s fs) -> (n : String) ->
                         FieldType (words n) ty fs -> Ptr ty
%extern
prim__setField : {s : _} -> forall fs, ty .
                         Ptr (Struct s fs) -> (n : String) ->
                         FieldType (words n) ty fs -> ty -> PrimIO ()

||| Retrieve the value of the specified field in the given `Struct`.
|||
||| @ s the `Struct` to retrieve the value from
||| @ n the name of the field in the `Struct`.
public export %inline
getField : {sn : _} -> (s : Ptr (Struct sn fs)) -> (n : String) ->
           {auto fieldok : FieldType (words n) ty fs} -> ty
getField s n = prim__getField s n fieldok

||| Retrieve the value of the specified field in the given `Struct` as a pointer.
|||
||| @ s the `Struct` to retrieve the value from
||| @ n the name of the field in the `Struct`.
public export %inline
getFieldPtr : {sn : _} -> (s : Ptr (Struct sn fs)) -> (n : String) ->
           {auto fieldok : FieldType (words n) ty fs} -> Ptr ty
getFieldPtr s n = prim__getFieldPtr s n fieldok

||| Set the value of the specified field in the given `Struct`.
|||
||| @ s   the `Struct` in which the field exists
||| @ n   the name of the field to set
||| @ val the value to set the field to
public export %inline
setField : {sn : _} -> (s : Ptr (Struct sn fs)) -> (n : String) ->
           {auto fieldok : FieldType (words n) ty fs} -> (val : ty) -> IO ()
setField s n val = primIO (prim__setField s n fieldok val)

%foreign "C:idris2_malloc, libidris2_support, idris_memory.h"
prim__malloc : (size : Int) -> PrimIO AnyPtr

%foreign "C:idris2_free, libidris2_support, idris_memory.h"
         "javascript:lambda:()=>undefined"
prim__free : AnyPtr -> PrimIO ()

||| Allocate memory with libc `malloc`.
|||
||| @ size the number of bytes to allocate
export
malloc : HasIO io => (size : Int) -> io AnyPtr
malloc size = primIO $ prim__malloc size

||| Release memory with libc `free`.
export
free : HasIO io => AnyPtr -> io ()
free ptr = primIO $ prim__free ptr
