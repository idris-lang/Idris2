module Control.Monad.State

import public Control.Monad.Identity
import public Control.Monad.Trans

||| A computation which runs in a context and produces an output
public export
interface Monad m => MonadState stateType (m : Type -> Type) | m where
    ||| Get the context
    get : m stateType
    ||| Write a new context/output
    put : stateType -> m ()

||| The transformer on which the State monad is based
public export
record StateT (stateType : Type) (m : Type -> Type) (a : Type) where
  constructor ST
  runStateT' : stateType -> m (stateType, a)

public export
implementation Functor f => Functor (StateT stateType f) where
    map f (ST g) = ST (\st => map (map f) (g st)) where

public export
implementation Monad f => Applicative (StateT stateType f) where
    pure x = ST (\st => pure (st, x))

    (ST f) <*> (ST a)
        = ST (\st =>
                do (r, g) <- f st
                   (t, b) <- a r
                   pure (t, g b))

public export
implementation Monad m => Monad (StateT stateType m) where
    (ST f) >>= k
        = ST (\st =>
                do (st', v) <- f st
                   let ST kv = k v
                   kv st')

public export
implementation Monad m => MonadState stateType (StateT stateType m) where
    get   = ST (\x => pure (x, x))
    put x = ST (\y => pure (x, ()))

public export
implementation MonadTrans (StateT stateType) where
    lift x
        = ST (\st =>
                do r <- x
                   pure (st, r))

public export
implementation (Monad f, Alternative f) => Alternative (StateT st f) where
    empty = lift empty
    (ST f) <|> (ST g) = ST (\st => f st <|> g st)

public export
implementation HasIO m => HasIO (StateT stateType m) where
  liftIO io = ST $ \s => liftIO $ io_bind io $ \a => pure (s, a)

||| Apply a function to modify the context of this computation
public export
modify : MonadState stateType m => (stateType -> stateType) -> m ()
modify f
    = do s <- get
         put (f s)

||| Evaluate a function in the context held by this computation
public export
gets : MonadState stateType m => (stateType -> a) -> m a
gets f
    = do s <- get
         pure (f s)

||| Unwrap and apply a StateT monad computation.
public export
%inline
runStateT : stateType -> StateT stateType m a -> m (stateType, a)
runStateT s act = runStateT' act s

||| The State monad. See the MonadState interface
public export
State : (stateType : Type) -> (ty : Type) -> Type
State = \s, a => StateT s Identity a

||| Unwrap and apply a State monad computation.
public export
runState : stateType -> StateT stateType Identity a -> (stateType, a)
runState s act = runIdentity (runStateT s act)

||| Unwrap and apply a State monad computation, but discard the final state.
public export
evalState : stateType -> State stateType a -> a
evalState s = snd . runState s

||| Unwrap and apply a State monad computation, but discard the resulting value.
public export
execState : stateType -> State stateType a -> stateType
execState s = fst . runState s
