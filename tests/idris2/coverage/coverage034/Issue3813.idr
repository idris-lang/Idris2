import System.FFI

public export
data FFICall : List Type -> Type -> Type where
  FCReturn :
    FFICall [] (PrimIO b)

  FCReturnVoid :
    FFICall [] (PrimIO ())

  FCSame :
    FFICall args f ->
    FFICall (a::args) (a -> f)

  FCInteger :
    Cast Integer a =>
    FFICall args f ->
    FFICall (Integer::args) (a -> f)

  FCDerefStructPtr :
    FFICall args f ->
    FFICall ((Ptr (Struct name fields))::args) (Struct name fields -> f)


public export
0 FFICallRet : FFICall args f -> Type
FFICallRet (FCReturn { b }) = b
FFICallRet (FCReturnVoid) = ()
FFICallRet (FCSame rest) = FFICallRet rest
FFICallRet (FCInteger rest) = FFICallRet rest
FFICallRet (FCDerefStructPtr rest) = FFICallRet rest
