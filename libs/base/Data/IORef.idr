module Data.IORef

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

export
newIORef : HasIO io => a -> io (IORef a)
newIORef val
    = do m <- primIO (prim__newIORef val)
         pure (MkRef m)

%inline
export
readIORef : HasIO io => IORef a -> io a
readIORef (MkRef m) = primIO (prim__readIORef m)

%inline
export
writeIORef : HasIO io => IORef a -> (val : a) -> io ()
writeIORef (MkRef m) val = primIO (prim__writeIORef m val)

%inline
export
writeIORef1 : HasLinearIO io => IORef a -> (1 val : a) -> io ()
writeIORef1 (MkRef m) val = primIO1 (prim__writeIORef m val)

export
modifyIORef : HasIO io => IORef a -> (a -> a) -> io ()
modifyIORef ref f
    = do val <- readIORef ref
         writeIORef ref (f val)
