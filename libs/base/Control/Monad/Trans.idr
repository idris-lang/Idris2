module Control.Monad.Trans

%default total

||| A monad transformer is a type that can wrap an inner monad, extending it
||| with additional abilities.
public export
interface MonadTrans t where
    ||| Lift a computation from the inner monad to the transformed monad.
    lift : Monad m => m a -> t m a
