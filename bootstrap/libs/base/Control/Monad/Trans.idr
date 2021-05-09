module Control.Monad.Trans

public export
interface MonadTrans t where
    lift : Monad m => m a -> t m a
