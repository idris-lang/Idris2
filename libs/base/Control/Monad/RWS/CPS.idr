||| Note: The difference to a 'stricht' RWST implementation is
||| that accumulation of values does not happen in the
||| Applicative and Monad instances but when invoking `Writer`-specific
||| functions like `writer` or `listen`.
module Control.Monad.RWS.CPS

import Control.Monad.Identity
import Control.Monad.Trans

||| A monad transformer adding reading an environment of type `r`,
||| collecting an output of type `w` and updating a state of type `s`
||| to an inner monad `m`.
public export
record RWST (r : Type) (w : Type) (s : Type) (m : Type -> Type) (a : Type) where
  constructor MkRWST
  unRWST : r -> s -> w -> m (a, s, w)

||| Unwrap an RWST computation as a function. (The inverse of `rwsT`.)
public export %inline
runRWST : Monoid w => RWST r w s m a -> r -> s -> m (a, s, w)
runRWST m r s = unRWST m r s neutral

||| Construct an RWST computation from a function. (The inverse of `runRWST`.)
public export %inline
rwsT : (Functor m, Semigroup w) => (r -> s -> m (a, s, w)) -> RWST r w s m a
rwsT f = MkRWST $ \r,s,w => (\(a,s',w') => (a,s',w <+> w')) <$> f r s

||| Evaluate a computation with the given initial state and environment,
||| returning the final value and output, discarding the final state.
public export %inline
evalRWST : (Functor m, Monoid w) => RWST r w s m a -> r -> s -> m (a,w)
evalRWST m r s = (\(a,_,w) => (a,w)) <$> runRWST m r s

||| Evaluate a computation with the given initial state and environment,
||| returning the final state and output, discarding the final value.
public export %inline
execRWST : (Functor m, Monoid w) => RWST r w s m a -> r -> s -> m (s,w)
execRWST m r s = (\(_,s',w) => (s',w)) <$> runRWST m r s

||| Map the inner computation using the given function.
public export %inline
mapRWST : (Functor n, Monoid w, Semigroup w')
        => (m (a, s, w) -> n (b, s, w')) -> RWST r w s m a -> RWST r w' s n b
mapRWST f m = MkRWST \r,s,w =>
                (\(a,s',w') => (a,s',w <+> w')) <$> f (runRWST m r s)

||| `withRWST f m` executes action `m` with an initial environment
||| and state modified by applying `f`.
public export %inline
withRWST : (r' -> s -> (r, s)) -> RWST r w s m a -> RWST r' w s m a
withRWST f m = MkRWST \r,s => uncurry (unRWST m) (f r s)

--------------------------------------------------------------------------------
--          RWS Functions
--------------------------------------------------------------------------------

||| A monad containing an environment of type `r`, output of type `w`
||| and an updatable state of type `s`.
public export
RWS : (r : Type) -> (w : Type) -> (s : Type) -> (a : Type) -> Type
RWS r w s = RWST r w s Identity

||| Unwrap an RWS computation as a function. (The inverse of `rws`.)
public export %inline
runRWS : Monoid w => RWS r w s a -> r -> s -> (a, s, w)
runRWS m r s = runIdentity (runRWST m r s)

||| Construct an RWS computation from a function. (The inverse of `runRWS`.)
public export %inline
rws : Semigroup w => (r -> s -> (a, s, w)) -> RWS r w s a
rws f = MkRWST \r,s,w => let (a, s', w') = f r s
                          in Id (a, s', w <+> w')

||| Evaluate a computation with the given initial state and environment,
||| returning the final value and output, discarding the final state.
public export %inline
evalRWS : Monoid w => RWS r w s a -> r -> s -> (a,w)
evalRWS m r s = let (a,_,w) = runRWS m r s
                 in (a,w)

||| Evaluate a computation with the given initial state and environment,
||| returning the final state and output, discarding the final value.
public export %inline
execRWS : Monoid w => RWS r w s a -> r -> s -> (s,w)
execRWS m r s = let (_,s1,w) = runRWS m r s
                 in (s1,w)

||| Map the return value, final state and output of a computation using
||| the given function.
public export %inline
mapRWS :  (Monoid w, Semigroup w')
       => ((a, s, w) -> (b, s, w')) -> RWS r w s a -> RWS r w' s b
mapRWS f = mapRWST (Id . f . runIdentity)

||| `withRWS f m` executes action `m` with an initial environment
||| and state modified by applying `f`.
public export %inline
withRWS : (r' -> s -> (r, s)) -> RWS r w s a -> RWS r' w s a
withRWS = withRWST

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
Functor m => Functor (RWST r w s m) where
  map f m = MkRWST \r,s,w => (\(a,s',w') => (f a,s',w')) <$> unRWST m r s w

public export %inline
Monad m => Applicative (RWST r w s m) where
  pure a = MkRWST \_,s,w => pure (a,s,w)
  MkRWST mf <*> MkRWST mx =
    MkRWST \r,s,w => do (f,s1,w1) <- mf r s w
                        (a,s2,w2) <- mx r s1 w1
                        pure (f a,s2,w2)

public export %inline
(Monad m, Alternative m) => Alternative (RWST r w s m) where
  empty = MkRWST \_,_,_ => empty
  MkRWST m <|> MkRWST n = MkRWST \r,s,w => m r s w <|> n r s w

public export %inline
Monad m => Monad (RWST r w s m) where
  m >>= k = MkRWST \r,s,w => do (a,s1,w1) <- unRWST m r s w 
                                unRWST (k a) r s1 w1

public export %inline
MonadTrans (RWST r w s) where
  lift m = MkRWST \_,s,w => map (\a => (a,s,w)) m

public export %inline
HasIO m => HasIO (RWST r w s m) where
  liftIO = lift . liftIO

--------------------------------------------------------------------------------
--          Reader Operations
--------------------------------------------------------------------------------

||| Retrieve a function of the current environment.
public export %inline
asks : Applicative m => (r -> a) -> RWST r w s m a
asks f = MkRWST \r,s,w => pure (f r,s,w)

||| Constructor for computations in the reader monad (equivalent to `asks`).
public export %inline
reader : Applicative m => (r -> a) -> RWST r w s m a
reader = asks

||| Fetch the value of the environment.
public export %inline
ask : Applicative m => RWST r w s m r
ask = asks id

||| Execute a computation in a modified environment
public export %inline
local : (r -> r) -> RWST r w s m a -> RWST r w s m a
local f m = MkRWST \r,s,w => unRWST m (f r) s w

--------------------------------------------------------------------------------
--          Writer Operations
--------------------------------------------------------------------------------

||| Construct a writer computation from a (result, output) pair.
public export %inline
writer : (Semigroup w, Applicative m) => (a, w) -> RWST r w s m a
writer (a,w') = MkRWST \_,s,w => pure (a,s,w <+> w')

||| `tell w` is an action that produces the output `w`.
public export %inline
tell : (Semigroup w, Applicative m) => w -> RWST r w s m ()
tell w' = writer ((), w')

||| `listens f m` is an action that executes the action `m` and adds
||| the result of applying `f` to the output to the value of the computation.
public export %inline
listens :  (Monoid w, Functor m)
        => (w -> b) -> RWST r w s m a -> RWST r w s m (a, b)
listens f m = MkRWST \r,s,w =>
                (\(a,s',w') => ((a,f w'),s',w <+> w')) <$> runRWST m r s

||| `listen m` is an action that executes the action `m` and adds its
||| output to the value of the computation.
public export %inline
listen :  (Monoid w, Functor m)
       => RWST r w s m a -> RWST r w s m (a, w)
listen = listens id

||| `pass m` is an action that executes the action `m`, which returns
||| a value and a function, and returns the value, applying the function
||| to the output.
public export %inline
pass : (Monoid w, Semigroup w', Functor m)
     => RWST r w s m (a, w -> w') -> RWST r w' s m a
pass m = MkRWST \r,s,w =>
           (\((a,f),s',w') => (a,s',w <+> f w')) <$> runRWST m r s

||| `censor f m` is an action that executes the action `m` and
||| applies the function `f` to its output, leaving the return value
||| unchanged.
public export %inline
censor : (Monoid w, Functor m) => (w -> w) -> RWST r w s m a -> RWST r w s m a
censor f m = MkRWST \r,s,w =>
               (\(a,s',w') => (a,s',w <+> f w')) <$> runRWST m r s

--------------------------------------------------------------------------------
--          Writer Operations
--------------------------------------------------------------------------------

||| Construct a state monad computation from a state transformer function.
public export %inline
state : Applicative m => (s -> (a, s)) -> RWST r w s m a
state f = MkRWST \_,s,w => let (a,s') = f s in pure (a,s',w)

||| Get a specific component of the state, using a projection function
||| supplied.
public export %inline
gets : Applicative m =>(s -> a) -> RWST r w s m a
gets f = MkRWST \_,s,w => pure (f s,s,w)

||| Fetch the current value of the state within the monad.
public export %inline
get : Applicative m =>RWST r w s m s
get = gets id

||| `put s` sets the state within the monad to `s`.
public export %inline
put : Applicative m => s -> RWST r w s m ()
put s = MkRWST \_,_,w => pure ((),s,w)

||| `modify f` is an action that updates the state to the result of
||| applying `f` to the current state.
public export %inline
modify : Applicative m =>(s -> s) -> RWST r w s m ()
modify f = MkRWST \_,s,w => pure ((),f s,w)
