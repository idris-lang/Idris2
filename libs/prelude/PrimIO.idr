module PrimIO

import Builtin

public export
data IORes : Type -> Type where
     MkIORes : (result : a) -> (1 x : %World) -> IORes a

||| Idris's primitive IO, for building abstractions on top of.
public export
PrimIO : Type -> Type
PrimIO a = (1 x : %World) -> IORes a

export
data IO : Type -> Type where
     MkIO : (1 fn : PrimIO a) -> IO a

export
prim_io_pure : a -> PrimIO a
prim_io_pure x = \w => MkIORes x w

%inline
export
io_pure : a -> IO a
io_pure x = MkIO (\w => MkIORes x w)

export
prim_io_bind : (1 act : PrimIO a) -> (1 k : a -> PrimIO b) -> PrimIO b
prim_io_bind fn k w
    = let MkIORes x' w' = fn w in k x' w'

-- There's a special case for inlining this is Compiler.Inline, because
-- the inliner is cautious about case blocks at the moment. Once it's less
-- cautious, add an explicit %inline directive and take out the special case.
-- See also dealing with the newtype optimisation via %World in
-- Compiler.CompileExpr
export
io_bind : (1 act : IO a) -> (1 k : a -> IO b) -> IO b
io_bind (MkIO fn) k
    = MkIO (\w => let MkIORes x' w' = fn w
                      MkIO res = k x' in
                      res w')

%foreign "C:putchar,libc 6"
prim__putChar : Char -> (1 x : %World) -> IORes ()
%foreign "C:getchar,libc 6"
%extern prim__getChar : (1 x : %World) -> IORes Char

-- A pointer representing a given parameter type
-- The parameter is a phantom type, to help differentiate between
-- different pointer types
public export
data Ptr : Type -> Type where [external]

-- A pointer to any type (representing a void* in foreign calls)
public export
data AnyPtr : Type where [external]

public export
data ThreadID : Type where [external]

public export
data FArgList : Type where
     Nil : FArgList
     (::) : {a : Type} -> (1 arg : a) -> (1 args : FArgList) -> FArgList

%extern prim__cCall : (ret : Type) -> String -> (1 args : FArgList) ->
                      (1 x : %World) -> IORes ret
%extern prim__schemeCall : (ret : Type) -> String -> (1 args : FArgList) ->
                           (1 x : %World) -> IORes ret

export %inline
primIO : (1 fn : (1 x : %World) -> IORes a) -> IO a
primIO op = MkIO op

export %inline
toPrim : (1 act : IO a) -> PrimIO a
toPrim (MkIO fn) = fn

export %inline
schemeCall : (ret : Type) -> String -> (1 args : FArgList) -> IO ret
schemeCall ret fn args = primIO (prim__schemeCall ret fn args)

export %inline
cCall : (ret : Type) -> String -> FArgList -> IO ret
cCall ret fn args = primIO (prim__cCall ret fn args)

%foreign "C:idris2_isNull, libidris2_support"
export
prim__nullAnyPtr : AnyPtr -> Int

prim__forgetPtr : Ptr t -> AnyPtr
prim__forgetPtr = believe_me

export %inline
prim__nullPtr : Ptr t -> Int -- can't pass 'type' to a foreign function
prim__nullPtr p = prim__nullAnyPtr (prim__forgetPtr p)

%foreign "C:idris2_getString, libidris2_support"
export
prim__getString : Ptr String -> String

%foreign "C:idris2_getStr,libidris2_support"
prim__getStr : PrimIO String
%foreign "C:idris2_putStr,libidris2_support"
prim__putStr : String -> PrimIO ()

||| Output a string to stdout without a trailing newline.
export
putStr : String -> IO ()
putStr str = primIO (prim__putStr str)

||| Output a string to stdout with a trailing newline.
export
putStrLn : String -> IO ()
putStrLn str = putStr (prim__strAppend str "\n")

||| Read one line of input from stdin, without the trailing newline.
export
getLine : IO String
getLine = primIO prim__getStr

||| Write a single character to stdout.
export
putChar : Char -> IO ()
putChar c = primIO (prim__putChar c)

||| Write a single character to stdout, with a trailing newline.
export
putCharLn : Char -> IO ()
putCharLn c = putStrLn (prim__cast_CharString c)

||| Read a single character from stdin.
export
getChar : IO Char
getChar = primIO prim__getChar

export
fork : (1 prog : IO ()) -> IO ThreadID
fork (MkIO act) = schemeCall ThreadID "blodwen-thread" [act]

export
prim_fork : (1 prog : PrimIO ()) -> PrimIO ThreadID
prim_fork act w = prim__schemeCall ThreadID "blodwen-thread" [act] w

%foreign "C:idris2_readString, libidris2_support"
export
prim__getErrno : Int

unsafeCreateWorld : (1 f : (1 x : %World) -> a) -> a
unsafeCreateWorld f = f %MkWorld

unsafeDestroyWorld : (1 x : %World) -> a -> a
unsafeDestroyWorld %MkWorld x = x

export
unsafePerformIO : IO a -> a
unsafePerformIO (MkIO f)
    = unsafeCreateWorld (\w => case f w of
                               MkIORes res w' => unsafeDestroyWorld w' res)
