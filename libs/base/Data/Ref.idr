module Data.Ref

import public Data.IORef
import public Control.Monad.ST

public export
interface Ref m (r : Type -> Type) | m where
  newRef : a -> m (r a)
  readRef : r a -> m a
  writeRef : r a -> a -> m ()

export
Ref IO IORef where
  newRef = newIORef
  readRef = readIORef
  writeRef = writeIORef

export
Ref (ST s) (STRef s) where
  newRef = newSTRef
  readRef = readSTRef
  writeRef = writeSTRef
