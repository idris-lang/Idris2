||| Provides mutable references as described in Lazy Functional State Threads.
module Control.Monad.ST

import Data.IORef

%default total

||| A mutable reference, bound to a state thread.
|||
||| A value of type `STRef s a` contains a mutable `a`, bound to a "thread"
||| `s`. Any access to the reference must occur in an `ST s` monad with the
||| same "thread".
export
data STRef : Type -> Type -> Type where
     MkSTRef : IORef a -> STRef s a

||| The `ST` monad allows for mutable access to references, but unlike `IO`, it
||| is "escapable".
|||
||| The parameter `s` is a "thread" -- it ensures that access to mutable
||| references created in each thread must occur in that same thread.
export
data ST : Type -> Type -> Type where
     MkST : IO a -> ST s a

||| Run a `ST` computation.
export
runST : (forall s . ST s a) -> a
runST p
    = let MkST prog = p {s = ()} in -- anything will do :)
          unsafePerformIO prog

export
Functor (ST s) where
  map fn (MkST st) = MkST $ fn <$> st

export
Applicative (ST s) where
  pure = MkST . pure
  MkST f <*> MkST a = MkST $ f <*> a

export
Monad (ST s) where
  MkST p >>= k
      = MkST $ do p' <- p
                  let MkST kp = k p'
                  kp

||| Create a new mutable reference with the given value.
export
newSTRef : a -> ST s (STRef s a)
newSTRef val
    = MkST $ do r <- newIORef val
                pure (MkSTRef r)

||| Read the value of a mutable reference.
|||
||| This occurs within `ST s` to prevent `STRef`s from being usable if they are
||| "leaked" via `runST`.
%inline
export
readSTRef : STRef s a -> ST s a
readSTRef (MkSTRef r) = MkST $ readIORef r

||| Write to a mutable reference.
%inline
export
writeSTRef : STRef s a -> (val : a) -> ST s ()
writeSTRef (MkSTRef r) val = MkST $ writeIORef r val

||| Apply a function to the contents of a mutable reference.
export
modifySTRef : STRef s a -> (a -> a) -> ST s ()
modifySTRef ref f
    = do val <- readSTRef ref
         writeSTRef ref (f val)
