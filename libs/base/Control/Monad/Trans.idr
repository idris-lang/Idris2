module Control.Monad.Trans

%default total

public export
interface MonadTrans t where
    lift : Monad m => m a -> t m a
