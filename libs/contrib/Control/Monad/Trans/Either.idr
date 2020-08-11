module Control.Monad.Trans.Either

%default total


public export
record EitherT m a b where
    constructor MkEitherT
    runEitherT : m (Either a b)

export
Functor m => Functor (EitherT m a) where
    map f (MkEitherT runEitherT) = MkEitherT (map (map f) runEitherT)

export
Monad m => Applicative (EitherT m a) where
    pure = MkEitherT . pure . Right
    (MkEitherT left) <*> (MkEitherT right) = MkEitherT $ do
        l <- left
        r <- right
        pure (l <*> r)

export
Monad m => Monad (EitherT m a) where
    join (MkEitherT runEitherT) = MkEitherT $ do
        case !runEitherT of
            Left l => pure (Left l)
            Right (MkEitherT inner) => inner


export
eitherT : Monad m => (a -> m c) -> (b -> m c) -> EitherT m a b -> m c
eitherT f g (MkEitherT runEitherT) = case !runEitherT of
    Left l => f l
    Right r => g r

export
bimapEitherT : Functor m => (a -> c) -> (b -> d) -> EitherT m a b -> EitherT m c d
bimapEitherT f g (MkEitherT runEitherT) = MkEitherT (map m runEitherT)
    where
    m : Either a b -> Either c d
    m (Left l) = Left (f l)
    m (Right r) = Right (g r)

export
mapEitherT : (m (Either a b) -> n (Either c d)) -> EitherT m a b -> EitherT n c d
mapEitherT f (MkEitherT runEitherT) = MkEitherT $ f runEitherT

export
hoist : Applicative m => Either a b -> EitherT m a b
hoist e = MkEitherT $ pure e

export
fail : Applicative m => a -> EitherT m a b
fail = MkEitherT . pure . Left
