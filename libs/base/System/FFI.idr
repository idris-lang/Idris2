-- Additional FFI help for more interesting C types
-- Some assumptions are made about the existence of this module in
-- Compiler.CompileExpr

module System.FFI

export
data Struct : String -> -- C struct name
              List (String, Type) -> -- field names and types
              Type where

public export
data FieldType : String -> Type -> List (String, Type) -> Type where
     First : FieldType n t ((n, t) :: ts)
     Later : FieldType n t ts -> FieldType n t (f :: ts)

%extern
prim__getField : {s : _} -> forall fs, ty . 
                         Struct s fs -> (n : String) ->
                         FieldType n ty fs -> ty
%extern
prim__setField : {s : _} -> forall fs, ty . 
                         Struct s fs -> (n : String) ->
                         FieldType n ty fs -> ty -> PrimIO ()

public export %inline
getField : {s : _} -> Struct s fs -> (n : String) ->
           {auto fieldok : FieldType n ty fs} -> ty
getField s n = prim__getField s n fieldok

public export %inline
setField : {s : _} -> Struct s fs -> (n : String) ->
           {auto fieldok : FieldType n ty fs} -> ty -> IO ()
setField s n val = primIO (prim__setField s n fieldok val)

