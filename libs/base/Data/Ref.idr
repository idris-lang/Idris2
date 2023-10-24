module Data.Ref

import public Data.IORef
import public Control.Monad.ST
import Control.Monad.State.Interface

%default total

public export
interface Ref m r | m where
  newRef : {0 a : Type} -> a -> m (r a)
  readRef : {0 a : Type} -> r a -> m a
  writeRef : r a -> a -> m ()

export
HasIO io => Ref io IORef where
  newRef = newIORef
  readRef = readIORef
  writeRef = writeIORef

export
Ref (ST s) (STRef s) where
  newRef = newSTRef
  readRef = readSTRef
  writeRef = writeSTRef

namespace MonadState

  export
  ForRef : Ref m r => Monad m => r a -> MonadState a m
  ForRef ref = MS where
    %inline
    [MS] MonadState a m where
      get = readRef ref
      put = writeRef ref
