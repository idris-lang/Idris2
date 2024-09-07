module Data.IORef

import System.Concurrency
import System.Info

%default total

-- Implemented externally
-- e.g., in Scheme, passed around as a box
data Mut : Type -> Type where [external]

%extern prim__newIORef : forall a . a -> (1 x : %World) -> IORes (Mut a)
%extern prim__readIORef : forall a . Mut a -> (1 x : %World) -> IORes a
%extern prim__writeIORef : forall a . Mut a -> (1 val : a) -> (1 x : %World) -> IORes ()

export
data IORef : Type -> Type where
     MkRef : Mut a -> IORef a

||| Create a new IORef.
export
newIORef : HasIO io => a -> io (IORef a)
newIORef val
    = do m <- primIO (prim__newIORef val)
         pure (MkRef m)

||| Read the value of an IORef.
%inline
export
readIORef : HasIO io => IORef a -> io a
readIORef (MkRef m) = primIO (prim__readIORef m)

||| Write a new value into an IORef.
||| This function does not create a memory barrier and can be reordered with other independent reads and writes within a thread,
||| which may cause issues for multithreaded execution.
%inline
export
writeIORef : HasIO io => IORef a -> (val : a) -> io ()
writeIORef (MkRef m) val = primIO (prim__writeIORef m val)

||| Write a new value into an IORef.
||| This function does not create a memory barrier and can be reordered with other independent reads and writes within a thread,
||| which may cause issues for multithreaded execution.
%inline
export
writeIORef1 : HasLinearIO io => IORef a -> (1 val : a) -> io ()
writeIORef1 (MkRef m) val = primIO1 (prim__writeIORef m val)

||| Mutate the contents of an IORef, combining readIORef and writeIORef.
||| This is not an atomic update, consider using atomicModifyIORef when operating in a multithreaded environment.
export
modifyIORef : HasIO io => IORef a -> (a -> a) -> io ()
modifyIORef ref f
    = do val <- readIORef ref
         writeIORef ref (f val)

||| This function atomically modifies the contents of an IORef.
||| This function is useful for using IORef in a safe way in a multithreaded program.
||| If you only have one IORef, then using atomicModifyIORef to access and modify it will prevent race conditions.
||| Any backend other than the default (chez) will perform modifyIORef (non-atomic).
export
atomicModifyIORef : HasIO io => IORef a -> (a -> a) -> io ()
atomicModifyIORef ref f
    = case codegen of
        "chez" => do mutex <- makeMutex
                     mutexAcquire mutex
                     val   <- readIORef ref
                     writeIORef ref (f val)
                     mutexRelease mutex
        _      => modifyIORef ref f
