||| The Error monad (also called the Exception monad).
module Control.Monad.Error.Interface

import Control.Monad.Error.Either

||| The strategy of combining computations that can throw exceptions
||| by bypassing bound functions
||| from the point an exception is thrown to the point that it is handled.
||| Is parameterized over the type of error information and
||| the monad type constructor.
||| It is common to use `Either String` as the monad type constructor
||| for an error monad in which error descriptions take the form of strings.
||| In that case and many other common cases the resulting monad is already defined
||| as an instance of the 'MonadError' class.
public export
interface Monad m => MonadError e m | m where
  ||| Is used within a monadic computation to begin exception processing.
  throwError : e -> m a

  ||| A handler function to handle previous errors and return to normal execution.
  ||| A common idiom is:
  |||
  ||| ```idris example
  ||| do { action1; action2; action3 } `catchError` handler
  ||| ```
  catchError : m a -> (e -> m a) -> m a

||| Lifts an `Either e` into any `MonadError e`.
public export
liftEither : MonadError e m => Either e a -> m a
liftEither = either throwError pure

||| Makes a success or failure of an action visible in
||| the return type.
public export
tryError : MonadError e m => m a -> m (Either e a)
tryError action = (map Right action) `catchError` (pure . Left)

||| `MonadError` analogue to the `withEitherT` function.
||| Modify the value (but not the type) of an error.
||| If you need to change the type of `e` use `mapError`.
public export
withError : MonadError e m => (e -> e) -> m a -> m a
withError f action = tryError action >>= either (throwError . f) pure

||| Flipped version of `catchError`.
public export
handleError : MonadError e m => (e -> m a) -> m a -> m a
handleError = flip catchError

||| `MonadError` analogue of the `mapEitherT` function.  The
||| computation is unwrapped, a function is applied to the `Either`, and
||| the result is lifted into the second `MonadError` instance.
public export
mapError : (MonadError e m, MonadError e' n)
         => (m (Either e a) -> n (Either e' b)) -> m a -> n b
mapError f action = f (tryError action) >>= liftEither

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
MonadError () Maybe where
  throwError ()        = Nothing
  catchError Nothing f = f ()
  catchError x       _ = x

public export
MonadError e (Either e) where
  throwError             = Left
  Left  l `catchError` h = h l
  Right r `catchError` _ = Right r

-- instance Monad m => MonadError e (ExceptT e m) where
--     throwError = ExceptT.throwE
--     catchError = ExceptT.catchE
-- 
-- -- ---------------------------------------------------------------------------
-- -- Instances for other mtl transformers
-- --
-- -- All of these instances need UndecidableInstances,
-- -- because they do not satisfy the coverage condition.
-- 
-- instance MonadError e m => MonadError e (IdentityT m) where
--     throwError = lift . throwError
--     catchError = Identity.liftCatch catchError
-- 
-- instance MonadError e m => MonadError e (MaybeT m) where
--     throwError = lift . throwError
--     catchError = Maybe.liftCatch catchError
-- 
-- instance MonadError e m => MonadError e (ReaderT r m) where
--     throwError = lift . throwError
--     catchError = Reader.liftCatch catchError
-- 
-- instance (Monoid w, MonadError e m) => MonadError e (LazyRWS.RWST r w s m) where
--     throwError = lift . throwError
--     catchError = LazyRWS.liftCatch catchError
-- 
-- instance (Monoid w, MonadError e m) => MonadError e (StrictRWS.RWST r w s m) where
--     throwError = lift . throwError
--     catchError = StrictRWS.liftCatch catchError
-- 
-- instance MonadError e m => MonadError e (LazyState.StateT s m) where
--     throwError = lift . throwError
--     catchError = LazyState.liftCatch catchError
-- 
-- instance MonadError e m => MonadError e (StrictState.StateT s m) where
--     throwError = lift . throwError
--     catchError = StrictState.liftCatch catchError
-- 
-- instance (Monoid w, MonadError e m) => MonadError e (LazyWriter.WriterT w m) where
--     throwError = lift . throwError
--     catchError = LazyWriter.liftCatch catchError
-- 
-- instance (Monoid w, MonadError e m) => MonadError e (StrictWriter.WriterT w m) where
--     throwError = lift . throwError
--     catchError = StrictWriter.liftCatch catchError
-- 
-- #if MIN_VERSION_transformers(0,5,6)
-- -- | @since 2.3
-- instance (Monoid w, MonadError e m) => MonadError e (CPSRWS.RWST r w s m) where
--     throwError = lift . throwError
--     catchError = CPSRWS.liftCatch catchError
-- 
-- -- | @since 2.3
-- instance (Monoid w, MonadError e m) => MonadError e (CPSWriter.WriterT w m) where
--     throwError = lift . throwError
--     catchError = CPSWriter.liftCatch catchError
-- #endif
-- 
-- #if MIN_VERSION_transformers(0,5,3)
-- -- | @since 2.3
-- instance
--   ( Monoid w
--   , MonadError e m
-- #if !MIN_VERSION_base(4,8,0)
--   , Functor m
-- #endif
--   ) => MonadError e (AccumT w m) where
--     throwError = lift . throwError
--     catchError = Accum.liftCatch catchError
-- #endif
-- 
