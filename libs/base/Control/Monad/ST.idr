module Control.Monad.ST

import Data.IORef

export
data STRef : Type -> Type -> Type where
     MkSTRef : IORef a -> STRef s a

export
data ST : Type -> Type -> Type where
     MkST : IO a -> ST s a

export
runST : (forall s . ST s a) -> a
runST p
    = let MkST prog = p {s = ()} in -- anything will do :)
          unsafePerformIO prog

mutual
  export
  Functor (ST s) where
    map fn st = pure $ fn !st

  export
  Applicative (ST s) where
    pure x = MkST (pure x)
    (<*>) f a = pure $ !f !a

  export
  Monad (ST s) where
    MkST p >>= k
        = MkST $ do p' <- p
                    let MkST kp = k p'
                    kp

export
newSTRef : a -> ST s (STRef s a)
newSTRef val
    = MkST $ do r <- newIORef val
                pure (MkSTRef r)

%inline
export
readSTRef : STRef s a -> ST s a
readSTRef (MkSTRef r) = MkST $ readIORef r

%inline
export
writeSTRef : STRef s a -> (val : a) -> ST s ()
writeSTRef (MkSTRef r) val = MkST $ writeIORef r val

export
modifySTRef : STRef s a -> (a -> a) -> ST s ()
modifySTRef ref f
    = do val <- readSTRef ref
         writeSTRef ref (f val)
