||| Provides a monad transformer `EitherT` that extends an inner monad with the
||| ability to throw and catch exceptions.

module Control.Monad.Error.Either

import Control.Monad.Trans

%default total

||| A monad transformer extending an inner monad with the ability to throw and
||| catch exceptions.
|||
||| Sequenced actions produce an exception if either action produces an
||| exception, with preference for the first exception. If neither produce an
||| exception, neither does the sequence of actions.
|||
||| `MaybeT m a` is equivalent to `EitherT () m a`, that is, an computation
||| that can only throw a single, information-less exception.
public export
data EitherT : (e : Type) -> (m : Type -> Type) -> (a : Type) -> Type where
  MkEitherT : m (Either e a) -> EitherT e m a

||| Unwrap an `EitherT` computation.
public export
%inline
runEitherT : EitherT e m a -> m (Either e a)
runEitherT (MkEitherT x) = x

||| Run an `EitherT` computation, handling results and exceptions with seperate
||| functions.
|||
||| This is a version of `either` lifted to work with `EitherT`.
public export
eitherT : Monad m => (a -> m c) -> (b -> m c) -> EitherT a m b -> m c
eitherT f g x = runEitherT x >>= either f g

||| Map over the underlying monadic computation.
public export
%inline
mapEitherT : (m (Either e a) -> n (Either e' a')) -> EitherT e m a -> EitherT e' n a'
mapEitherT f = MkEitherT . f . runEitherT

||| Map over the result or the exception of a monadic computation.
public export
bimapEitherT : Functor m => (a -> c) -> (b -> d)
            -> EitherT a m b -> EitherT c m d
bimapEitherT f g x = mapEitherT (map (either (Left . f) (Right . g))) x

||| A version of `Left` lifted to work with `EitherT`.
|||
||| This is equivalent to `throwE`.
public export
%inline
left : Applicative m => e -> EitherT e m a
left = MkEitherT . pure . Left

||| A version of `Right` lifted to work with `EitherT`.
|||
||| This is equivalent to `pure`.
public export
%inline
right : Applicative m => a -> EitherT e m a
right = MkEitherT . pure . Right

||| Swap the result and the exception of a monadic computation.
public export
swapEitherT : Functor m => EitherT e m a -> EitherT a m e
swapEitherT = mapEitherT (map (either Right Left))

-------------------------------------------------
-- Methods of the 'exception' theme
-------------------------------------------------

||| Throw an exception in a monadic computation.
public export
%inline
throwE : Applicative m => e -> EitherT e m a
throwE = MkEitherT . pure . Left

||| Handle an exception thrown in a monadic computation.
|||
||| Since the handler catches all errors thrown in the computation, it may
||| raise a different exception type.
public export
catchE : Monad m => EitherT e m a -> (e -> EitherT e' m a) -> EitherT e' m a
catchE et f
  = MkEitherT $ runEitherT et >>= either (runEitherT . f) (pure . Right)


-------------------------------------------------
-- Interface Implementations
-------------------------------------------------

public export
Eq (m (Either e a)) => Eq (EitherT e m a) where
 (==) = (==) `on` runEitherT

public export
Ord (m (Either e a)) => Ord (EitherT e m a) where
 compare = compare `on` runEitherT

public export
Show (m (Either e a)) => Show (EitherT e m a) where
  showPrec d (MkEitherT x) = showCon d "MkEitherT" $ showArg x

-- I'm not actually confident about having this instance but it is a sane
-- default and since idris has named implementations it can be swapped out at
-- the use site.
public export
Monad m => Semigroup (EitherT e m a) where
  MkEitherT x <+> MkEitherT y = MkEitherT $ do
    r@(Right _) <- x
      | Left _ => y
    pure r

public export
Functor m => Functor (EitherT e m) where
  map f e = MkEitherT $ map f <$> runEitherT e

public export
Foldable m => Foldable (EitherT e m) where
  foldr f acc (MkEitherT e)
    = foldr (\x,xs => either (const xs) (`f` xs) x) acc e

  null (MkEitherT e) = null e

public export
Traversable m => Traversable (EitherT e m) where
  traverse f (MkEitherT x)
    = MkEitherT <$> traverse (either (pure . Left) (map Right . f)) x

public export
Applicative m => Applicative (EitherT e m) where
  pure = MkEitherT . pure . Right
  f <*> x = MkEitherT [| runEitherT f <*> runEitherT x |]

public export
Monad m => Monad (EitherT e m) where
  x >>= k = MkEitherT $ runEitherT x >>= either (pure . Left) (runEitherT . k)

||| Alternative instance that collects left results, allowing you to try
||| multiple possibilities and combine failures.
public export
(Monad m, Monoid e) => Alternative (EitherT e m) where
  empty = left neutral
  MkEitherT x <|> my = MkEitherT $ do
    Left l <- x
      | Right r => pure (Right r)
    Left l' <- runEitherT my
      | Right r => pure (Right r)
    pure (Left (l <+> l'))

public export
MonadTrans (EitherT e) where
  lift = MkEitherT . map Right

public export
HasIO m => HasIO (EitherT e m) where
  liftIO act = MkEitherT $ liftIO (io_bind act (pure . Right))
