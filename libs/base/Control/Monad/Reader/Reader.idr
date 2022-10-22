module Control.Monad.Reader.Reader

import Control.Monad.Identity
import Control.Monad.Trans

%default total

||| A monad transformer extending an inner monad with access to an environment.
|||
||| The environment is the same for all actions in a sequence, but may be
||| changed within scopes created by `Control.Monad.Reader.local`.
public export
record ReaderT (stateType : Type) (m : Type -> Type) (a : Type) where
  constructor MkReaderT
  1 runReaderT' : stateType -> m a

||| Transform the computation inside a @ReaderT@.
public export %inline
mapReaderT : (m a -> n b) -> ReaderT r m a -> ReaderT r n b
mapReaderT f m = MkReaderT $ \st => f (runReaderT' m st)

||| Unwrap and apply a ReaderT monad computation
public export
%inline
runReaderT : stateType -> ReaderT stateType m a -> m a
runReaderT s action = runReaderT' action s

--------------------------------------------------------------------------------
--          Reader
--------------------------------------------------------------------------------

||| A monad that can access an environment.
|||
||| This is `ReaderT` applied to `Identity`.
public export
Reader : (stateType : Type) -> (a : Type) -> Type
Reader s = ReaderT s Identity

||| Unwrap and apply a Reader monad computation
public export %inline
runReader : stateType -> Reader stateType a -> a
runReader s = runIdentity . runReaderT s

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
implementation Functor f => Functor (ReaderT stateType f) where
  map f (MkReaderT g) = MkReaderT $ \st => f <$> g st

public export
implementation Applicative f => Applicative (ReaderT stateType f) where
  pure x = MkReaderT $ \_ => pure x

  MkReaderT f <*> MkReaderT a =
    MkReaderT $ \st =>
      let f' = f st in
      let a' = a st in
      f' <*> a'

public export
implementation Monad m => Monad (ReaderT stateType m) where
  MkReaderT f >>= k =
    MkReaderT $ \st => f st >>= runReaderT st . k

public export
implementation MonadTrans (ReaderT stateType) where
  lift x = MkReaderT $ \_ => x

public export
implementation HasIO m => HasIO (ReaderT stateType m) where
  liftIO f = MkReaderT $ \_ => liftIO f

public export
implementation Alternative f => Alternative (ReaderT stateType f) where
  empty = MkReaderT $ const empty

  MkReaderT f <|> mg = MkReaderT $ \st => f st <|> runReaderT' mg st
